#include <iostream>
#include "assert.h"

#include "smt.h"
#include "z3_sort.h"
#include "z3++.h"

#include "z3_factory.h"

using namespace smt;
using namespace std;
//using namespace z3;

int main()
{
	// z3::context c2; 
	// z3::context *c3 = &c2;
	// z3::sort x = c3->bool_sort();

	cout << "before solver creation " << endl;
	SmtSolver s = Z3SolverFactory::create(false);
	cout << "after solver creation " << endl;
	Sort boolsort1 = s->make_sort(BOOL);
	cout << "testing!!! :)" << endl;
	return 0;
}
