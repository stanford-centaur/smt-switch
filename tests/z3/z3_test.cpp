#include <iostream>
#include "assert.h"

#include "smt.h"
//#include "z3_sort.h"
//#include "z3++.h"

#include "z3_factory.h"

using namespace smt;
using namespace std;
//using namespace z3;

int main()
{
	SmtSolver s = Z3SolverFactory::create(false);
//	Sort bvsort8 = s->make_sort(BV, 8);
	cout << "testing!!! :)" << endl;
	return 0;
}
