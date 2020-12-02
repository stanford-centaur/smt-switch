#include <iostream>
#include "assert.h"

#include "smt.h"
#include "z3_sort.h"

#include "z3_factory.h"

using namespace smt;
using namespace std;
//using namespace z3;

int main() {
	SmtSolver s = Z3SolverFactory::create(false);

	cout << "sort testing: " << endl;
	Sort boolsort1 = s->make_sort(BOOL);
	Sort boolsort2 = s->make_sort(BOOL);
	Sort realsort = s->make_sort(REAL);
	Sort intsort = s->make_sort(INT);
	cout << boolsort1 << endl << realsort << endl << intsort << endl;

	Sort bvsort = s->make_sort(BV, 8);
	cout << bvsort << endl;

	Sort uninterpretedsort = s->make_sort("a test", 0);
	cout << uninterpretedsort << endl;

	Sort arraysort = s->make_sort(ARRAY, intsort, bvsort);
	cout << arraysort << endl;

	Sort functionsort = s->make_sort(FUNCTION, SortVec{ boolsort1, intsort, realsort, boolsort1 } );
	cout << functionsort << endl;

//	cout << functionsort->compare(intsort) << boolsort1->compare(boolsort2) << endl;

	cout << "testing done :)" << endl;

	return 0;
}
