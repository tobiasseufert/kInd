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

#ifndef IC3_h_INCLUDED
#define IC3_h_INCLUDED

#include "Model.h"

namespace kInd
{

enum kInd_result
{
	SAFE, CEX, CTI
};

kInd_result check(Model &model, int verbose = 0, // 0: silent, 1: stats, 2: informative
		bool basic = false,    // simple inductive generalization
		bool random = false,   // random runs for statistical profiling
		bool certificationMode = false, //certify a k-induction result ...
		unsigned int kToCertify = 1, //with a supposedly "kToCertify"-inductive property
		const char* dimacsFolder = ""); //write dimacs output into specific folder

void negateAndRedoCNF(vector<LitVec> &cnf, int nvars);

}

#endif
