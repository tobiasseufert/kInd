# kInd
This is plain k-induction without unrolling. The algorithm is based on k-Ind from *k-Induction without Unrolling* (Gurfinkel, Ivrii, FMCAD 2017). There is a minor tweak that we extended it to a complete model checking algorithm by gradually incrementing k.

# Build instructions

Download z lib.
Download the latest aiger release (e.g., https://github.com/arminbiere/aiger)
into folder aiger (do not make).

    cd minisat
    mkdir build
    cd build
    cmake -DCMAKE_BUILD_TYPE=Release ..  
    make
    cd ../..
    mkdir build
    cd build
    cmake -DCMAKE_BUILD_TYPE=Release ..  
    make

# Run

    Usage: ./kind [options] < problem.aig
    [options]:
    -v: verbose
    -s: print statistics
    -r: randomize SAT solver decision heuristics
    -b: use basic UNSAT generalization (irrelevant for proof obligations)
    -c: certify k-induction result (create a 1-inductive strengthening of P)
    -k [number]: the k for certification. Not required for model checking, ignored without -c option.
