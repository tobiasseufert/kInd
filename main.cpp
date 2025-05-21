/*********************************************************************
 Copyright (c) 2013, Aaron Bradley

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

#include <iostream>
#include <string>
#include <time.h>

extern "C" {
#include "aiger.h"
}
#include "kInd.h"
#include "Model.h"

void printHelp()
{
	cout << "This is plain k-induction without unrolling. \n"
			"The algorithm is based on k-Ind from *k-Induction without Unrolling* (Gurfinkel, Ivrii, FMCAD 2017).\n"
			"There is a minor tweak that we extended it to a complete model checking algorithm\n"
			"by gradually incrementing k.\n"
			"There is also an option (-c) which may certify whether a property is k-inductive \n"
			"(specified by a natural number after option -k)." << endl;
	cout << endl;
	cout << "Input is restricted to AIGER specifications and is redirected to stdin by the < operator." << endl;
	cout << endl;
	cout << "(Tobias Seufert, University of Freiburg, 2023)" << endl;
	cout << endl;
	cout << "Usage: ./kind [options] < problem.aig" << endl;
	cout << "[options]:" << endl;
	cout << "-v: verbose" << endl;
	cout << "-s: print statistics" << endl;
	cout << "-r: randomize SAT solver decision heuristics" << endl;
	cout << "-b: use basic UNSAT generalization (irrelevant for proof obligations)" << endl;
	cout << "-c: certify k-induction result (create a 1-inductive strengthening of P)" << endl;
	cout << "-k [number]: the k for certification. Not required for model checking, ignored without -c option." << endl;
}

int main(int argc, char **argv)
{
	unsigned int propertyIndex = 0, kToCertify = 1;
	bool basic = false, random = false, certificationMode = false;
	const char* dimacs_path = "";
	int verbose = 0;
	for (int i = 1; i < argc; ++i)
	{
		if (string(argv[i]) == "-v")
			// option: verbosity
			verbose = 2;
		else if (string(argv[i]) == "-s")
			// option: print statistics
			verbose = max(1, verbose);
		else if (string(argv[i]) == "-r")
		{
			// option: randomize the run, which is useful in performance
			// testing; default behavior is deterministic
			srand(time(NULL));
			random = true;
		}
		else if (string(argv[i]) == "-b")
			// option: use basic generalization
			basic = true;
		else if (string(argv[i]) == "-h" || string(argv[i]) == "--help")
		{
			//print usage
			printHelp();
			return 1;
		}
		else if (string(argv[i]) == "-c")
			// option: certification mode (certify that property is k-inductive, k is given, default: k = 1)
			certificationMode = true;
		else if (string(argv[i]) == "-k")
		{
			// option: certification mode (certify that property is k-inductive, k is given, default: k = 1)
			int val = atoi(argv[i + 1]);
			if (val <= 0)
			{
				cout
						<< "ERROR: (option -k recognized) k may only assume positive integers greater than 0."
						<< endl;
				return 0;
			}
			kToCertify = val;
			if (kToCertify == 0)
			{
				kToCertify = 1;
				cout
						<< "Certifying k = 0 is not implemented, set to default (k=1) instead."
						<< endl;
			}
			i++; //skip
		}
		else if (string(argv[i]) == "-o")
		{
			// option: specify output path
			const char* path = argv[i + 1];
			if (path[0] == '-' || path[0] == '<')
			{
				cout
						<< "ERROR: (option -o recognized) please specify valid path."
						<< endl;
				return 0;
			}
			dimacs_path = path;
			cout << "If design is safe (result 0): write DIMACS files into folder: " << path << endl;
			i++; //skip
		}
		//fail!
		else if (!atoi(argv[i]) && string(argv[i]) != "0")
		{
			//distinguish genType
			cout << "ERROR: unrecognized option: " << string(argv[i]) << endl;
			cout << "Use -h or --help." << endl;
			exit(0);

		}
		else
			// optional argument: set property index
			propertyIndex = (unsigned) atoi(argv[i]);
	}
	if (!certificationMode && kToCertify > 1)
		cout
				<< "WARNING: custom k > 1 and disabled certification mode leads to incomplete model checking!\n"
						"Therefore, k will automatically be set to 1.\n"
						"Do you really not want a certificate?" << endl;

	// read AIGER model
	aiger *aig = aiger_init();
	const char *msg = aiger_read_from_file(aig, stdin);
	if (msg)
	{
		cout << msg << endl;
		return 1;
	}
	// create the Model from the obtained aig
	Model *model = modelFromAiger(aig, propertyIndex);
	aiger_reset(aig);
	if (!model)
		return 1;

	// model check it
	kInd::kInd_result rv = kInd::check(*model, verbose, basic, random,
			certificationMode, kToCertify, dimacs_path);
	// print 0/1 according to AIGER standard
	cout << rv << endl; // (0 = SAFE, 1 = CEX, 2 = CTI

	delete model;

/*#ifndef NDEBUG
	testing::InitGoogleTest();
	return RUN_ALL_TESTS();
#endif*/


	return 0;
}
