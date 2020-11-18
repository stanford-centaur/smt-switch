#include <iostream>
#include "assert.h"

#include "smt.h"
#include "z3_sort.h"
#include "z3++.h"

#include "z3_factory.h"

using namespace smt;
using namespace std;
//using namespace z3;

int main() {
	cout << "before solver creation " << endl;
	SmtSolver s = Z3SolverFactory::create(false);
	cout << "after solver creation " << endl;

	cout << "..." << endl;
	Sort boolsort1 = s->make_sort(BOOL);
	Sort realsort1 = s->make_sort(REAL);
	Sort intsort1 = s->make_sort(INT);
	cout << boolsort1 << endl << realsort1 << endl << intsort1 << endl;

	Sort bvsort = s->make_sort(BV, 8);
	cout << bvsort << endl;

	Sort uninterpretedsort = s->make_sort("a test", 0);
	cout << uninterpretedsort << endl;

	Sort arraysort = s->make_sort(ARRAY, intsort1, bvsort);
	cout << arraysort << endl;

	Sort functionsort = s->make_sort(FUNCTION, SortVec{ boolsort1, intsort1, realsort1, boolsort1 } );
	cout << functionsort << endl;

	cout << "testing done :)" << endl;

	return 0;
}
