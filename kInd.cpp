/*********************************************************************
 Copyright (c) 2023, Tobias Seufert

 Permission is hereby granted, free of charge, to any person obtaining
 a copy of this software and associated documentation files (the
 "Software"), to deal in the Software without restriction, including
 without limitation the rights to use, copy, modify, merge, publish,
 distribute, sublicense, and/or sell copies of the Software, and to
 permit persons to whom the Software is furnished to do so, subject to
 the following conditions:

 The above copyright notice and this permission notice shall be
 included in all copies or substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *********************************************************************/

#include <algorithm>
#include <iostream>
#include <set>
#include <cmath>
#include <sys/times.h>

#include "kInd.h"
#include "Solver.h"
#include "Vec.h"

/*
 * Codebase is from IC3ref -- originally.
 *
 * This is plain k-induction without unrolling.
 * The algorithm is based on k-Ind from *k-Induction without Unrolling* (Gurfinkel, Ivrii, FMCAD 2017).
 * There is a minor tweak that we extended it to a complete model checking algorithm
 * by gradually incrementing k.
 * There is also an option (-c) which may certify whether a property is k-inductive
 * (specified by a natural number after option -k).
 * */
namespace kInd
{

class kInd
{
public:
	kInd(Model &_model) :
			verbose(0), random(false), certificationMode(false), dimacs_print_folder(
					"/tmp"), model(_model), k(1), nextState(
					0), litOrder(), slimLitOrder(), numLits(0), numUpdates(0), maxDepth(
					1), maxCTGs(3), maxJoins(1 << 20), micAttempts(3), cexState(
					0), nQuery(0), nCTI(0), nCTG(0), nmic(0), startTime(0), satTime(
					0), nCoreReduced(0), nAbortJoin(0), nAbortMic(0), timer(0)
	{
		slimLitOrder.heuristicLitOrder = &litOrder;

		// construct lifting solver
		lifts = model.newSolver();
		// don't assert primed invariant constraints
		model.loadTransitionRelationNoError(*lifts, false);
		// assert notInvConstraints (in stateOf) when lifting
		notInvConstraints = Minisat::mkLit(lifts->newVar());
		Minisat::vec<Minisat::Lit> cls;
		cls.push(~notInvConstraints);
		for (LitVec::const_iterator i = model.invariantConstraints().begin();
				i != model.invariantConstraints().end(); ++i)
			cls.push(model.primeLit(~*i));
		lifts->addClause_(cls);

		// initialize frame
		init();
	}
	~kInd()
	{
		delete frame.consecution;
		delete lifts;
	}

	// The main loop.
	kInd_result check()
	{
		startTime = time();  // stats
		if (verbose > 1)
			cout << "Begin with k = " << k << endl;
		kInd_result result = strengthen();
		if (result == SAFE)
		{
			/*
			 * proof provided:
			 *
			 * print I, T, ~P, F, ~F
			 */
			if(strlen(dimacs_print_folder) > 0)
				printCNFs();
		}
		return result; // strengthen to remove < k inductive successors
	}

	// Follows and prints chain of states from cexState forward.
	void printWitness()
	{
		if (cexState != 0)
		{
			size_t curr = cexState;
			while (curr)
			{
				cout << stringOfLitVec(state(curr).inputs)
						<< stringOfLitVec(state(curr).latches) << endl;
				curr = state(curr).successor;
			}
		}
	}

private:

	int verbose; // 0: silent, 1: stats, 2: all
	bool random;
	bool certificationMode; // true: only certify a given k, false: complete model checking algorithm

	string stringOfLitVec(const LitVec &vec)
	{
		stringstream ss;
		for (LitVec::const_iterator i = vec.begin(); i != vec.end(); ++i)
			ss << model.stringOfLit(*i) << " ";
		return ss.str();
	}

	int litToDimacs(const Minisat::Lit lit) const
	{
		return (Minisat::var(lit) * pow(-1.0, Minisat::sign(lit)));
	}
	const char *dimacs_print_folder;
	void printToFile(std::string &output, const char *file_name) const
	{
		//oh no ...
		char *path = (char*) malloc(
				sizeof(char)
						* (strlen(dimacs_print_folder) + strlen("/")
								+ strlen(file_name) + 1));
		path[0] = '\0';
		strcat(path, dimacs_print_folder);
		strcat(path, "/");
		strcat(path, file_name);
		ofstream dimacsFile(path);
		if (dimacsFile.is_open())
		{
			dimacsFile << output;
			dimacsFile.close();
			if (verbose)
			{
				cout << "printed DIMACS file " << file_name << " to path: " << path
						<< endl;
			}
		}
		else
		{
			cerr << "Could not open file for DIMACS output." << endl;
		}
		free(path);
	}
	void printDimacsCNF(const vector<LitVec> &cnf, const char *file_name) const
	{
		std::string dimacsCNF = "";
		std::string dimacsHeader = "p cnf ";
		int maxvar = 0;
		int nCl = cnf.size();

		for (auto &clause : cnf)
		{
			if(clause.size() == 1 && Minisat::var(clause[0]) == 0)
			{
				--nCl;
				continue; //skip trail literal of trivial btrue()
			}
			for (auto &lit : clause)
			{
				dimacsCNF.append(std::to_string(litToDimacs(lit)) + " ");
				if(Minisat::var(lit) > maxvar)
					maxvar = Minisat::var(lit);
			}
			dimacsCNF.append("0\n");
		}

		dimacsHeader.append(std::to_string(maxvar) + " ");
		dimacsHeader.append(std::to_string(nCl) + "\n");
		dimacsHeader.append(dimacsCNF);
		printToFile(dimacsHeader, file_name);

	}
	//CNF of unary clauses (like initial state description)
	void printDimacsCNF(const LitVec &cnf, const char *file_name) const
	{
		std::string dimacsCNF = "";
		std::string dimacsHeader = "p cnf ";
		int maxvar = 0;
		size_t nCl = cnf.size();

		for (auto &lit : cnf)
		{
			if(Minisat::var(lit) == 0) continue; //skip trail literal of trivial btrue()
			dimacsCNF.append(std::to_string(litToDimacs(lit)) + " ");
			if(Minisat::var(lit) > maxvar)
				maxvar = Minisat::var(lit);
			dimacsCNF.append("0\n");
		}

		dimacsHeader.append(std::to_string(maxvar) + " ");
		dimacsHeader.append(std::to_string(nCl) + "\n");
		dimacsHeader.append(dimacsCNF);
		printToFile(dimacsHeader, file_name);
	}
	void printCNFs()
	{
		printDimacsCNF(model.initialState(), "init");
		vector<LitVec> cnf;
		vector<LitVec> cnfPlainF;
		vector<LitVec> cnfPrime;
		model.loadTransitionRelationToContainer(cnf);
		printDimacsCNF(cnf, "trans");
		cnf.clear();
		model.loadErrorToContainer(cnf);
		printDimacsCNF(cnf, "notP");
		cnf.clear();
		int maxvar = 0;
		for (auto &cube : frame.cubes)
		{
			LitVec cls;
			for (auto &lit : cube)
			{
				cls.push_back(~lit);
				if (maxvar < Minisat::var(lit))
					maxvar = Minisat::var(lit);
			}
			cnfPlainF.push_back(cls);
		}
		negateAndRedoCNF(cnfPlainF, maxvar);
		printDimacsCNF(cnfPlainF, "notF");
		cnfPlainF.clear();
		maxvar = 0;
		//F is conjoined to P implicitely (by adding P to T,
		//but F & P should also be able to stand alone)
		frame.cubes.insert({model.error()});
		for (auto &cube : frame.cubes)
		{
			LitVec cls;
			LitVec clsPrime;
			for (auto &lit : cube)
			{
				cls.push_back(~lit);
				clsPrime.push_back(~model.primeLit(lit));
				if (maxvar < Minisat::var(lit))
					maxvar = Minisat::var(lit);
			}
			cnf.push_back(cls);
			cnfPrime.push_back(clsPrime);
		}
		printDimacsCNF(cnf, "F");
		negateAndRedoCNF(cnfPrime,
				model.primeVar(model.varOfLit(Minisat::mkLit(maxvar, false))).var());
		printDimacsCNF(cnfPrime, "notFprime");
	}

	Model &model;
	size_t k;

	// The State structures are for tracking trees of (lifted) CTIs.
	// Because States are created frequently, I want to avoid dynamic
	// memory management; instead their (de)allocation is handled via
	// a vector-based pool.
	struct State
	{
		size_t successor;  // successor State
		LitVec latches;
		LitVec inputs;
		size_t index;      // for pool
		bool used;         // for pool
	};
	vector<State> states;
	size_t nextState;
	// WARNING: do not keep reference across newState() calls
	State& state(size_t sti)
	{
		return states[sti - 1];
	}
	size_t newState()
	{
		if (nextState >= states.size())
		{
			states.resize(states.size() + 1);
			states.back().index = states.size();
			states.back().used = false;
		}
		size_t ns = nextState;
		assert(!states[ns].used);
		states[ns].used = true;
		while (nextState < states.size() && states[nextState].used)
			nextState++;
		return ns + 1;
	}
	void delState(size_t sti)
	{
		State &st = state(sti);
		st.used = false;
		st.latches.clear();
		st.inputs.clear();
		if (nextState > st.index - 1)
			nextState = st.index - 1;
	}
	void resetStates()
	{
		for (vector<State>::iterator i = states.begin(); i != states.end(); ++i)
		{
			i->used = false;
			i->latches.clear();
			i->inputs.clear();
		}
		nextState = 0;
	}

	// A CubeSet is a set of ordered (by integer value) vectors of
	// Minisat::Lits.
	static bool _LitVecComp(const LitVec &v1, const LitVec &v2)
	{
		if (v1.size() < v2.size())
			return true;
		if (v1.size() > v2.size())
			return false;
		for (size_t i = 0; i < v1.size(); ++i)
		{
			if (v1[i] < v2[i])
				return true;
			if (v2[i] < v1[i])
				return false;
		}
		return false;
	}
	static bool _LitVecEq(const LitVec &v1, const LitVec &v2)
	{
		if (v1.size() != v2.size())
			return false;
		for (size_t i = 0; i < v1.size(); ++i)
			if (v1[i] != v2[i])
				return false;
		return true;
	}
	class LitVecComp
	{
	public:
		bool operator()(const LitVec &v1, const LitVec &v2) const
		{
			return _LitVecComp(v1, v2);
		}
	};
	typedef set<LitVec, LitVecComp> CubeSet;

	// A proof obligation.
	struct Obligation
	{
		Obligation(size_t st, size_t b) :
				state(st), budget(b)
		{
		}
		size_t state;  // Generalize this state...
		size_t budget;  // ... w.r.t. its consumed budget.
	};
	class ObligationComp //stack-like behaviour
	{
	public:
		bool operator()(const Obligation &o1, const Obligation &o2) const
		{
			if (o1.budget > o2.budget)
				return true;  // prefer higher budget consumption (required)
			if (o1.budget < o2.budget)
				return false;
			if (o1.state < o2.state)
				return true;  // canonical final decider
			return false;
		}
	};
	typedef set<Obligation, ObligationComp> PriorityQueue;

	// For IC3's overall frame structure.
	struct Frame
	{
		CubeSet cubes;  // additional cubes in this and previous frames
		Minisat::Solver *consecution;
	};
	Frame frame;

	Minisat::Solver *lifts;
	Minisat::Lit notInvConstraints;

	// Refresh Frame.
	void init()
	{
		frame.consecution = model.newSolver();
		if (random)
		{
			frame.consecution->random_seed = rand();
			frame.consecution->rnd_init_act = true;
		}
		model.loadTransitionRelation(*frame.consecution);
	}

	// Structure and methods for imposing priorities on literals
	// through ordering the dropping of literals in mic (drop leftmost
	// literal first) and assumptions to Minisat.  The implemented
	// ordering prefers to keep literals that appear frequently in
	// addCube() calls.
	struct HeuristicLitOrder
	{
		HeuristicLitOrder() :
				_mini(1 << 20)
		{
		}
		vector<float> counts;
		size_t _mini;
		void count(const LitVec &cube)
		{
			assert(!cube.empty());
			// assumes cube is ordered
			size_t sz = (size_t) Minisat::toInt(Minisat::var(cube.back()));
			if (sz >= counts.size())
				counts.resize(sz + 1);
			_mini = (size_t) Minisat::toInt(Minisat::var(cube[0]));
			for (LitVec::const_iterator i = cube.begin(); i != cube.end(); ++i)
				counts[(size_t) Minisat::toInt(Minisat::var(*i))] += 1;
		}
		void decay()
		{
			for (size_t i = _mini; i < counts.size(); ++i)
				counts[i] *= 0.99;
		}
	} litOrder;

	struct SlimLitOrder
	{
		HeuristicLitOrder *heuristicLitOrder;

		SlimLitOrder()
		{
		}

		bool operator()(const Minisat::Lit &l1, const Minisat::Lit &l2) const
		{
			// l1, l2 must be unprimed
			size_t i2 = (size_t) Minisat::toInt(Minisat::var(l2));
			if (i2 >= heuristicLitOrder->counts.size())
				return false;
			size_t i1 = (size_t) Minisat::toInt(Minisat::var(l1));
			if (i1 >= heuristicLitOrder->counts.size())
				return true;
			return (heuristicLitOrder->counts[i1]
					< heuristicLitOrder->counts[i2]);
		}
	} slimLitOrder;

	float numLits, numUpdates;
	void updateLitOrder(const LitVec &cube)
	{
		litOrder.decay();
		numUpdates += 1;
		numLits += cube.size();
		litOrder.count(cube);
	}

	// order according to preference
	void orderCube(LitVec &cube)
	{
		stable_sort(cube.begin(), cube.end(), slimLitOrder);
	}

	typedef Minisat::vec<Minisat::Lit> MSLitVec;

	// Orders assumptions for Minisat.
	void orderAssumps(MSLitVec &cube, bool rev, int start = 0)
	{
		stable_sort(cube + start, cube + cube.size(), slimLitOrder);
		if (rev)
			reverse(cube + start, cube + cube.size());
	}

	//ungeneralize a lifted cube genCube such that it holds that genCube => F.
	void ungeneralizeLiftedCube(LitVec &genCube, const LitVec &origCube) const
	{
#ifndef NDEBUG
		size_t oldsz = genCube.size();
		for(size_t i = 0; i < genCube.size() - 1; ++i)
		{
			assert(Minisat::toInt(genCube[i] < genCube[i+1]));
		}
		for(size_t i = 0; i < origCube.size() - 1; ++i)
		{
			assert(Minisat::toInt(origCube[i] < origCube[i+1]));
		}
		cout << "Sorted gencube vectors guaranteed." << endl;
#endif

		//it is asserted, that all cubes are sorted vectors of literals
		for (auto &blockedCube : frame.cubes)
		{
			bool disjoint = false;
			for (auto &lit : genCube)
			{
				if (std::binary_search(blockedCube.begin(), blockedCube.end(),
						~lit))
				{
					disjoint = true;
					break;
				}
			}
			if (!disjoint)
			{
				//intersection with blocked cubes?
				//find reason literal in original cube and add to generalized cube
				LitVec diff;
				diff.resize(origCube.size() - genCube.size());
				//always re-compute diff, since genCube is dynamically changing
				assert(diff.size() > 0); // in case of intersection: there has to be a diff, otherwise error
				std::set_difference(origCube.begin(), origCube.end(),
						genCube.begin(), genCube.end(), diff.begin());
				for (auto &lit : diff)
					if (std::binary_search(blockedCube.begin(),
							blockedCube.end(), ~lit))
						genCube.push_back(lit);
				std::sort(genCube.begin(), genCube.end());
			}
		}

#ifndef NDEBUG
		assert(genCube.size() >= oldsz);
#endif
	}

	// Assumes that last call to fr.consecution->solve() was
	// satisfiable.  Extracts state(s) cube from satisfying
	// assignment.
	size_t stateOf(size_t succ = 0)
	{
		// create state
		size_t st = newState();
		state(st).successor = succ;
		MSLitVec assumps;
		assumps.capacity(
				1 + 2 * (model.endInputs() - model.beginInputs())
						+ (model.endLatches() - model.beginLatches()));
		Minisat::Lit act = Minisat::mkLit(lifts->newVar()); // activation literal
		assumps.push(act);
		Minisat::vec<Minisat::Lit> cls;
		cls.push(~act);
		cls.push(notInvConstraints);  // successor must satisfy inv. constraint
		cls.push(model.error()); // predecessor must satisfy P
		if (succ == 0)
			cls.push(~model.primedError());
		else
			for (LitVec::const_iterator i = state(succ).latches.begin();
					i != state(succ).latches.end(); ++i)
				cls.push(model.primeLit(~*i));
		lifts->addClause_(cls);
		// extract and assert primary inputs
		for (VarVec::const_iterator i = model.beginInputs();
				i != model.endInputs(); ++i)
		{
			Minisat::lbool val = frame.consecution->modelValue(i->var());
			if (val != Minisat::l_Undef)
			{
				Minisat::Lit pi = i->lit(val == Minisat::l_False);
				state(st).inputs.push_back(pi);  // record full inputs
				assumps.push(pi);
			}
		}
		// some properties include inputs, so assert primed inputs after
		for (VarVec::const_iterator i = model.beginInputs();
				i != model.endInputs(); ++i)
		{
			Minisat::lbool pval = frame.consecution->modelValue(
					model.primeVar(*i).var());
			if (pval != Minisat::l_Undef)
				assumps.push(model.primeLit(i->lit(pval == Minisat::l_False)));
		}
		int sz = assumps.size();
		// extract and assert latches
		LitVec latches;
		for (VarVec::const_iterator i = model.beginLatches();
				i != model.endLatches(); ++i)
		{
			Minisat::lbool val = frame.consecution->modelValue(i->var());
			if (val != Minisat::l_Undef)
			{
				Minisat::Lit la = i->lit(val == Minisat::l_False);
				latches.push_back(la);
				assumps.push(la);
			}
		}
		orderAssumps(assumps, false, sz); // empirically found to be best choice
		// State s, inputs i, transition relation T, successor t:
		//   s & i & T & ~t' is unsat
		// Core assumptions reveal a lifting of s.
		++nQuery;
		startTimer();  // stats
		bool rv = lifts->solve(assumps);
		endTimer(satTime);
		assert(!rv);
		// obtain lifted latch set from unsat core
		for (LitVec::const_iterator i = latches.begin(); i != latches.end();
				++i)
			if (lifts->conflict.has(~*i))
				state(st).latches.push_back(*i);  // record lifted latches
		// deactivate negation of successor
		lifts->releaseVar(~act);

		/*
		 * collect only predecessors which satisfy F.
		 *
		 * Find intersections with cubes, re-add literals that
		 * make these disjoint.
		 */
		ungeneralizeLiftedCube(state(st).latches, latches);

		/*** debug TODO***/
#ifndef NDEBUG
		LitVec result;
		result.resize(state(st).latches.size());

		std::set_intersection(state(st).latches.begin(),
				state(st).latches.end(), latches.begin(), latches.end(),
				result.begin());

		assert(result == state(st).latches);

		Minisat::Solver *testSlv = model.newSolver();
		model.loadTransitionRelation(*testSlv);
		MSLitVec testassumps;
		for (auto &lit : state(st).latches)
			testassumps.push(lit);
		testassumps.push(model.error());
		bool testrv = testSlv->solve(testassumps);
		assert(!testrv);
		delete testSlv;

		bool disjoint;
		if (frame.cubes.size() > 0)
		{
			for (auto &blockedCube : frame.cubes)
			{
				disjoint = false;
				for (auto &lit : state(st).latches)
				{
					if (std::binary_search(blockedCube.begin(),
							blockedCube.end(), ~lit))
					{
						disjoint = true;
						break;
					}
				}
				if (!disjoint)
				{
					cout << "blocked cube: " << stringOfLitVec(blockedCube)
							<< endl;
					cout << "latches: " << stringOfLitVec(state(st).latches)
							<< endl;
				}
			}
			assert(disjoint);
		}
		cout << "Ungeneralization seems fine." << endl;
#endif
		/*************/

		return st;
	}

	// Checks if cube contains any initial states.
	bool initiation(const LitVec &latches)
	{
		return !model.isInitial(latches);
	}

	// Check if ~latches is inductive relative to frame fi.  If it's
	// inductive and core is provided, extracts the unsat core.  If
	// it's not inductive and pred is provided, extracts
	// predecessor(s).
	bool consecution(const LitVec &latches, size_t succ = 0,
			LitVec *core = NULL, size_t *pred = NULL)
	{
		MSLitVec assumps;
		LitVec cube;
		assumps.capacity(latches.size());
		for (LitVec::const_iterator i = latches.begin(); i != latches.end();
				++i)
		{
			cube.push_back(*i);
			assumps.push(*i);  // push unprimed...
		}
		// ... order... (empirically found to best choice)
		orderAssumps(assumps, false);
		// ... now prime
		for (int i = 0; i < assumps.size(); ++i)
			assumps[i] = model.primeLit(assumps[i]);
		addCube(cube, true);
		// F_fi & ~latches & T & latches'
		++nQuery;
		startTimer();  // stats
		bool rv = frame.consecution->solve(assumps);
		endTimer(satTime);
		if (rv)
		{
			// fails: extract predecessor(s)
			if (pred)
				*pred = stateOf(succ);
			return false;
		}
		// succeeds
		if (core)
		{
			for (LitVec::const_iterator i = latches.begin(); i != latches.end();
					++i)
				if (frame.consecution->conflict.has(~model.primeLit(*i)))
					core->push_back(*i);
			if (!initiation(*core))
				*core = latches;
		}
		return true;
	}

	bool consecutionIndgen(const LitVec &latches, size_t succ = 0,
			LitVec *core = NULL, size_t *pred = NULL, bool orderedCore = false)
	{
		/* Variant with activation literal. TODO: think about de-/activating chains of POs
		 *
		 */
		MSLitVec assumps, cls;
		assumps.capacity(1 + latches.size());
		cls.capacity(1 + latches.size());
		Minisat::Lit act = Minisat::mkLit(frame.consecution->newVar());
		assumps.push(act);
		cls.push(~act);
		for (LitVec::const_iterator i = latches.begin(); i != latches.end();
				++i)
		{
			cls.push(~*i);
			assumps.push(*i);  // push unprimed...
		}
		// ... order... (empirically found to best choice)
		if (pred)
			orderAssumps(assumps, false, 1);
		else
			orderAssumps(assumps, orderedCore, 1);
		// ... now prime
		for (int i = 1; i < assumps.size(); ++i)
			assumps[i] = model.primeLit(assumps[i]);

		frame.consecution->addClause_(cls);
		// F_fi & ~latches & T & latches'
		++nQuery;
		startTimer();  // stats
		bool rv = frame.consecution->solve(assumps);
		endTimer(satTime);
		if (rv)
		{
			// fails: extract predecessor(s)
			if (pred)
				*pred = stateOf(succ);
			frame.consecution->releaseVar(~act);
			return false;
		}
		if (core)
		{
			if (pred && orderedCore)
			{
				// redo with correctly ordered assumps
				reverse(assumps + 1, assumps + assumps.size());
				++nQuery;
				startTimer();  // stats
				rv = frame.consecution->solve(assumps);
				assert(!rv);
				endTimer(satTime);
			}
			for (LitVec::const_iterator i = latches.begin(); i != latches.end();
					++i)
				if (frame.consecution->conflict.has(~model.primeLit(*i)))
					core->push_back(*i);
			if (!initiation(*core))
				*core = latches;
		}
		frame.consecution->releaseVar(~act);
		return true;
	}

	size_t maxDepth, maxCTGs, maxJoins, micAttempts;

	// Based on
	//
	//   Zyad Hassan, Aaron R. Bradley, and Fabio Somenzi, "Better
	//   Generalization in IC3," (submitted May 2013)
	//
	// Improves upon "down" from the original paper (and the FMCAD'07
	// paper) by handling CTGs.
	bool ctgDown(LitVec &cube, size_t keepTo, size_t recDepth)
	{
		size_t ctgs = 0, joins = 0;
		while (true)
		{
			// induction check
			if (!initiation(cube))
				return false;
			if (recDepth > maxDepth)
			{
				// quick check if recursion depth is exceeded
				LitVec core;
				bool rv = consecutionIndgen(cube, 0, &core, NULL, true);
				if (rv && core.size() < cube.size())
				{
					++nCoreReduced;  // stats
					cube = core;
				}
				return rv;
			}
			// prepare to obtain CTG
			size_t cubeState = newState();
			state(cubeState).successor = 0;
			state(cubeState).latches = cube;
			size_t ctg;
			LitVec core;
			if (consecutionIndgen(cube, cubeState, &core, &ctg, true))
			{
				if (core.size() < cube.size())
				{
					++nCoreReduced;  // stats
					cube = core;
				}
				// inductive, so clean up
				delState(cubeState);
				return true;
			}
			// not inductive, address interfering CTG
			LitVec ctgCore;
			bool ret = false;
			if (ctgs < maxCTGs/* && level > 1*/&& initiation(state(ctg).latches)
					&& consecutionIndgen(state(ctg).latches, cubeState,
							&ctgCore))
			{
				// CTG is inductive relative to level-1; push forward and generalize
				++nCTG;  // stats
				++ctgs;
				/*size_t j = level;
				 // QUERY: generalize then push or vice versa?
				 while (j <= k && consecution(j, ctgCore))
				 ++j;*/
				mic(ctgCore, recDepth + 1);
				addCube(ctgCore);
			}
			else if (joins < maxJoins)
			{
				// ran out of CTG attempts, so join instead
				ctgs = 0;
				++joins;
				LitVec tmp;
				for (size_t i = 0; i < cube.size(); ++i)
					if (binary_search(state(ctg).latches.begin(),
							state(ctg).latches.end(), cube[i]))
						tmp.push_back(cube[i]);
					else if (i < keepTo)
					{
						// previously failed when this literal was dropped
						++nAbortJoin;  // stats
						ret = true;
						break;
					}
				cube = tmp;  // enlarged cube
			}
			else
				ret = true;
			// clean up
			delState(cubeState);
			delState(ctg);
			if (ret)
				return false;
		}
	}

	// Extracts minimal inductive (relative to level) subclause from
	// ~cube --- at least that's where the name comes from.  With
	// ctgDown, it's not quite a MIC anymore, but what's returned is
	// inductive relative to the possibly modifed level.
	void mic(LitVec &cube, size_t recDepth)
	{
		++nmic;  // stats
		// try dropping each literal in turn
		size_t attempts = micAttempts;
		orderCube(cube);
		for (size_t i = 0; i < cube.size();)
		{
			LitVec cp(cube.begin(), cube.begin() + i);
			cp.insert(cp.end(), cube.begin() + i + 1, cube.end());
			if (ctgDown(cp, i, recDepth))
			{
				// maintain original order
				LitSet lits(cp.begin(), cp.end());
				LitVec tmp;
				for (LitVec::const_iterator j = cube.begin(); j != cube.end();
						++j)
					if (lits.find(*j) != lits.end())
						tmp.push_back(*j);
				cube.swap(tmp);
				// reset attempts
				attempts = micAttempts;
			}
			else
			{
				if (!--attempts)
				{
					// Limit number of attempts: if micAttempts literals in a
					// row cannot be dropped, conclude that the cube is just
					// about minimal.  Definitely improves mics/second to use
					// a low micAttempts, but does it improve overall
					// performance?
					++nAbortMic;  // stats
					return;
				}
				++i;
			}
		}
	}

	// wrapper to start inductive generalization
	void mic(LitVec &cube)
	{
		mic(cube, 1);
	}

	// Adds cube to frames at and below level, unless !toAll, in which
	// case only to level.
	void addCube(LitVec &cube, bool silent = false)
	{
		sort(cube.begin(), cube.end());
		pair<CubeSet::iterator, bool> rv = frame.cubes.insert(cube);
		if (!rv.second)
			return;
		if (!silent && verbose > 1)
			cout << "new cube: " << stringOfLitVec(cube) << endl;
		MSLitVec cls;
		cls.capacity(cube.size());
		for (LitVec::const_iterator i = cube.begin(); i != cube.end(); ++i)
			cls.push(~*i);
		frame.consecution->addClause(cls);
		if (!silent)
			updateLitOrder(cube);
	}

	// ~cube was found to be inductive relative to level; now see if
	// we can do better.
	void generalize(LitVec cube)
	{
		// generalize
		mic(cube);
		addCube(cube);
	}

	size_t cexState;  // beginning of counterexample trace

	// Process obligations according to priority.
	kInd_result handleObligations(PriorityQueue obls)
	{
		while (!obls.empty())
		{
			PriorityQueue::iterator obli = obls.begin();
			Obligation obl = *obli;
			LitVec core;
			size_t predi;

#ifndef NDEBUG
			//rule out loops ...
			bool disjoint;
			for (PriorityQueue::const_iterator it = next(obls.begin(), 1);
					it != obls.end(); ++it)
			{
				disjoint = false;
				for (auto &lit : state(obl.state).latches)
				{
					if (std::binary_search(state(it->state).latches.begin(),
							state(it->state).latches.end(), ~lit))
					{
						disjoint = true;
						break;
					}
				}
				if (!disjoint)
				{
					cout << "po in prioqueue: "
							<< stringOfLitVec(state(it->state).latches) << endl;
					cout << "current po: "
							<< stringOfLitVec(state(obl.state).latches) << endl;
				}
			}
			assert(disjoint);
			cout << "No Loops guaranteed." << endl;
#endif

			//Determine if counterexample to:
			if (model.isInitial(state(obl.state).latches))
			{
				// 1. k-invariant (some ~P-state is reachable within up to k steps)
				//		-> unsafe
				cexState = obl.state;
				return CEX;
			}
			if (obl.budget == k) //a POB has used up its budget ...
			{
				// 2. k-inductive (some ~P-state is reachable in more than k steps)
				//		-> increase k (or certification failed)
				if (certificationMode)
				{
#ifndef NDEBUG
					//TEST in debug mode
					Minisat::Solver *testSlv = model.newSolver();
					model.loadTransitionRelation(*testSlv);
					size_t currStateCex = obl.state;
					LitVec currCube;
					LitVec nextCube;
					LitVec inp;
					MSLitVec assumps;
					size_t nextStateCex;
					int length = k;
					vector <LitVec> CTIchain;
					CTIchain.push_back(state(currStateCex).latches);
					while(true)
					{
						if(currStateCex)
						{
							nextStateCex = state(currStateCex).successor;
							if(!nextStateCex) break;
							inp = state(currStateCex).inputs;
							currCube = state(currStateCex).latches;
						}
						else break;
						if(nextStateCex)
						{
							nextCube = state(nextStateCex).latches;
							CTIchain.push_back(nextCube);
						}

						for(auto& lit: currCube)
							assumps.push(lit);
						for(auto& lit: inp)
							assumps.push(lit);
						for(auto& lit: nextCube)
							assumps.push(model.primeLit(lit));

						bool sat = testSlv->solve(assumps);
						assumps.clear();
						cout << "checked " << length-- << "th element of CTI chain." << endl;
						assert(sat);

						currStateCex = nextStateCex;
					}

					delete testSlv;

					//guarantee no loops (naive, only for debugging purposes)
					for(size_t k = 0; k < CTIchain.size(); ++k)
					{
						for(size_t l = 0; l < CTIchain.size(); ++l)
						{
							if(k!=l)
							{
								disjoint = false;
								for (auto &lit : CTIchain[k])
								{
									if (std::binary_search(CTIchain[l].begin(), CTIchain[l].end(), ~lit))
									{
										disjoint = true;
										break;
									}
								}
								assert(disjoint);
							}
						}
					}

#endif
					return CTI;
				}
				//not k-inductive: increase k (TODO: handle failed certification attempt)
				k++; // complete model checking algorithm: increase k
				printStats();
			}

			// Is the obligation fulfilled?
			if (consecution(state(obl.state).latches, obl.state, &core, &predi))
			{
				// Yes,
				obls.erase(obli);
				//generalize and block.
				generalize(core);
			}
			else
			{
				++nCTI;  // stats
				// No, so focus on predecessor.
				obls.insert(Obligation(predi, obl.budget + 1));
			}
		}
		return SAFE;
	}

	// Strengthens frontier to remove error successors.
	kInd_result strengthen()
	{
		while (true)
		{
			++nQuery;
			startTimer();  // stats
			bool rv = frame.consecution->solve(model.primedError());
			endTimer(satTime);
			if (!rv)
			{
				buildCertifaiger(frame);
				return SAFE;
			}
			// handle CTI with error successor
			++nCTI;  // stats
			PriorityQueue pq;
			// enqueue main obligation and handle
			pq.insert(Obligation(stateOf(), 1));
			switch (handleObligations(pq))
			{
			case CEX: //found real counterexample, system is unsafe w.r.t. P
				return CEX;
			case CTI:
				return CTI;
			default:
				break;
			}
			// finished with States for this iteration, so clean up
			resetStates();
		}
	}

	int currNewAigMaxVar = model.getAigMaxVar();
	vector<Minisat::Lit> cubeAnds;
	void buildCertifaiger(const Frame & frame)
	{
		aiger *aig = aiger_init();
		for(VarVec::const_iterator i = model.beginInputs(); i != model.endInputs(); ++i)
		{
			aiger_add_input(aig, Minisat::toInt(i->lit(false)), i->name().c_str());
		}
		for(VarVec::const_iterator i = model.beginLatches(); i != model.endLatches(); ++i)
		{
			aiger_add_latch(aig, Minisat::toInt(i->lit(false)), Minisat::toInt(model.nextStateFn(*i)),  i->name().c_str());
		}
		for(AigVec::const_iterator a = model.beginAnds(); a != model.endAnds(); ++a)
		{
			aiger_add_and(aig, Minisat::toInt(a->lhs), Minisat::toInt(a->rhs0), Minisat::toInt(a->rhs1));
		}
		assert(cubeAnds.size() == 0);
		for (CubeSet::iterator j = frame.cubes.begin();
				j != frame.cubes.end(); ++j)
		{
			aigerAndsOfCube(aig, *j);
		}
		finalBigOr(aig);

		aiger_check(aig);
		int ret = aiger_open_and_write_to_file(aig, "./certificate.aag");
		assert(ret);

		aiger_reset(aig);
	}

	// cube = (l1 * l2* ... ) => andi = (...(((l1 * l2) * l3) * l4) ... )
	void aigerAndsOfCube(aiger * aig, const LitVec & cube)
	{
		if(cube.size() > 1)
		{
			for (size_t i = 0; i < cube.size() - 1; ++i)
			{
				++currNewAigMaxVar;
				aiger_add_and(aig, 2*currNewAigMaxVar, ((i==0) ? Minisat::toInt(cube[i]) : (2*(currNewAigMaxVar-1))), Minisat::toInt(cube[i+1]));
			}
			cubeAnds.push_back(Minisat::mkLit(currNewAigMaxVar, false));
		}
		else
		{
			assert(cube.size() == 1);
			cubeAnds.push_back(cube[0]);
		}
	}

	// error + and1 + and2 + ... (strengthening property)
	void finalBigOr(aiger * aig)
	{
		assert(cubeAnds.size() >= 1);
		++currNewAigMaxVar;
		aiger_add_and(aig, 2*currNewAigMaxVar, Minisat::toInt(~model.error()), Minisat::toInt(~cubeAnds[0])); // OR (negate operands and output) 

		if(cubeAnds.size() > 1)
		{
			for (size_t i = 0; i < cubeAnds.size() - 1; ++i)
			{
				++currNewAigMaxVar;
				aiger_add_and(aig, 2*currNewAigMaxVar, 2*(currNewAigMaxVar-1), Minisat::toInt(~cubeAnds[i+1]));
			}
		}
		aiger_add_output(aig, 2*currNewAigMaxVar+1, "O_cert"); //negated because of OR
	}

	int nQuery, nCTI, nCTG, nmic;
	clock_t startTime, satTime;
	int nCoreReduced, nAbortJoin, nAbortMic;
	clock_t time()
	{
		struct tms t;
		times(&t);
		return t.tms_utime;
	}
	clock_t timer;
	void startTimer()
	{
		timer = time();
	}
	void endTimer(clock_t &t)
	{
		t += (time() - timer);
	}
	void printStats()
	{
		if (!verbose)
			return;
		clock_t etime = time();
		cout << ". Elapsed time: " << ((double) etime / sysconf(_SC_CLK_TCK))
				<< endl;
		etime -= startTime;
		if (!etime)
			etime = 1;
		cout << ". % SAT:        "
				<< (int) (100 * (((double) satTime) / ((double) etime)))
				<< endl;
		cout << ". K:            " << k << endl;
		cout << ". # Queries:    " << nQuery << endl;
		cout << ". # CTIs:       " << nCTI << endl;
		cout << ". # CTGs:       " << nCTG << endl;
		cout << ". # mic calls:  " << nmic << endl;
		cout << ". Queries/sec:  "
				<< (int) (((double) nQuery) / ((double) etime)
						* sysconf(_SC_CLK_TCK)) << endl;
		cout << ". Mics/sec:     "
				<< (int) (((double) nmic) / ((double) etime)
						* sysconf(_SC_CLK_TCK)) << endl;
		cout << ". # Red. cores: " << nCoreReduced << endl;
		cout << ". # Int. joins: " << nAbortJoin << endl;
		cout << ". # Int. mics:  " << nAbortMic << endl;
		if (numUpdates)
			cout << ". Avg lits/cls: " << numLits / numUpdates << endl;
	}

	friend kInd_result check(Model&, int, bool, bool, bool, unsigned int,
			const char*);

};

// IC3 does not check for 0-step and 1-step reachability, so do it
// separately.
bool baseCases(Model &model)
{
	Minisat::Solver *base0 = model.newSolver();
	model.loadInitialCondition(*base0);
	model.loadError(*base0);
	bool rv = base0->solve(model.error());
	delete base0;
	if (rv)
		return false;

	Minisat::Solver *base1 = model.newSolver();
	model.loadInitialCondition(*base1);
	model.loadTransitionRelation(*base1);
	rv = base1->solve(model.primedError());
	delete base1;
	if (rv)
		return false;

	model.lockPrimes();

	return true;
}

// External function to make the magic happen.
kInd_result check(Model &model, int verbose, bool basic, bool random,
		bool certificationMode, unsigned int kToCertify,
		const char *dimacsFolder)
{
	if (!baseCases(model))
	{
		if (certificationMode)
			cout << "Certification of " << kToCertify
					<< "-inductive property failed.";
		return CEX;
	}
	kInd kind(model);
	kind.verbose = verbose;
	kind.certificationMode = certificationMode;
	kind.dimacs_print_folder = dimacsFolder;
	if (certificationMode)
	{
		kind.k = kToCertify;
	}
	if (basic)
	{
		kind.maxDepth = 0;
		kind.maxJoins = 0;
		kind.maxCTGs = 0;
	}
	if (random)
		kind.random = true;
	kInd_result rv = kind.check();
	if (rv != SAFE && verbose > 1)
		kind.printWitness(); //TODO: comprehensive witness for CTI ...
	if (verbose)
		kind.printStats();
	if (rv == CTI && certificationMode)
		cout << "k-CTI: Certification of " << kToCertify
				<< "-inductive property failed." << endl;
	if (rv == CEX && certificationMode)
		cout << "CEX!!: Certification of " << kToCertify
				<< "-inductive property failed." << endl;
	return rv; // SAFE = 0, CEX = 1, CTI = 2
}

//Negate and PG-transform
void negateAndRedoCNF(vector<LitVec> &cnf, int maxvar)
{
	/*
	 * Negate cnf (result is a dnf), transform back into CNF.
	 * We assume that the top level variable is true, i.e.
	 * that the resulting formula has to evaluate to true, i.e. ~cnf.
	 *
	 * Expects that maxvar contains the highest variable index of cnf
	 */

	LitVec auxLits;
	vector<LitVec> pgTransform;
	unsigned int current_aux = maxvar + 1; //auxiliary variable index
	for (auto &clause : cnf)
	{
		Minisat::Lit aux_lit = Minisat::mkLit(current_aux, false);
		++current_aux;
		auxLits.push_back(aux_lit);
		for (auto &lit : clause)
		{
			assert(Minisat::var(lit) <= maxvar);
			LitVec cl;
			cl.push_back(~lit); //negated! and then transformed
			cl.push_back(~aux_lit);
			pgTransform.push_back(cl); //~Inv clause
		}
	}

	//Combining s_all <-> (c1 + c2 + ... )
	LitVec generalFullCl;
	for (auto &auxLit : auxLits)
	{
		generalFullCl.push_back(auxLit);
	}
	pgTransform.push_back(generalFullCl);

	cnf.swap(pgTransform);
}

}
