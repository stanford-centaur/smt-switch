#include <iostream>
#include "assert.h"

#include "smt.h"
#include "z3_sort.h"

#include "z3_factory.h"

using namespace smt;
using namespace std;
//using namespace z3;

void print_vec(string name, TermVec ts) {
	cout << name << ": ";
	for(int i = 0; i < ts.size(); i++){
		cout << ts[i] << " ";
	}
	cout << endl;
}

int main() {
	cout << "before solver creation " << endl;
	SmtSolver s = Z3SolverFactory::create(false);
	cout << "after solver creation " << endl;

	cout << "* * * sort testing * * *" << endl;
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

	cout << "* * * end sort testing * * *" << endl << "* * * term testing * * *" << endl;

	Term boolterm1 = s-> make_term(true);
	Term boolterm2 = s-> make_term(false);
	cout << boolterm1 << endl;
	cout << boolterm2 << endl;

	Term intterm = s->make_term(1, intsort1);
	Term realterm = s->make_term(2, realsort1);
	Term bvterm = s->make_term(8, bvsort);
	cout << intterm << endl;
	cout << realterm << endl;
	cout << bvterm << endl;

	cout << "to int:" << endl;
	cout << intterm->to_int() << endl;
	cout << realterm->to_int() << endl;
	cout << bvterm->to_int() << endl;

	cout << "* * * end term testing * * *" << endl;

	context c;
	expr bv_const_test = c.bv_const("bv!", 8);
	expr bv_val_test = c.bv_val("2", 8);
	expr constx = c.constant("x", c.bool_sort());

	cout << "const:  " << bv_const_test << endl;
	cout << "val:  " << bv_val_test << endl;
	cout << "c - c  " << bv_const_test.is_const() << endl;
	cout << "c - n  " << bv_const_test.is_numeral() << endl;
	cout << "c - v  " << bv_const_test.is_var() << endl;
	cout << "v - c  " << bv_val_test.is_const() << endl;
	cout << "v - n  " << bv_val_test.is_numeral() << endl;
	cout << "c - v  " << bv_val_test.is_var() << endl;
	cout << "x - v  " << constx.is_var() << endl;

	cout << "testing done :)" << endl;

	cout << "ops testing: " << endl;


	Term notBool = s->make_term(Not, boolterm1);
	Term isInt = s->make_term(Is_Int, intterm);
	cout << notBool << endl;
	cout << isInt << endl;

	//AND
	Z3_ast args[2];
	args[0] = c.bool_val(true);
	args[1] = c.bool_val(true);
	Z3_ast testand = Z3_mk_and(c, 2, args);
	expr ex = expr(c, testand);
	cout << "*  " << testand << endl;
	cout << "*  " << ex << endl;


	Term impl = s->make_term(Implies, boolterm1, boolterm1);
	Term andBool = s->make_term(And, boolterm1, boolterm2);
	Term concat = s->make_term(Concat, bvterm, bvterm);
	cout << impl << endl;
	cout << andBool << endl;
	cout << concat << endl;

//	Op e = Op(Extract, 3, 0);
//	Term ext = s->make_term(e, bvterm);
//	cout << ext << endl;
	cout << " * " << endl;


//	z3::context c;
	z3::expr a = c.bv_val(12, 16);
	cout << a << endl;
	Z3_ast a0 = Z3_mk_extract(a.ctx(),3,0,a);
	Z3_ast a1 = Z3_mk_extract(a.ctx(),3,0,c.bv_val("2", 8));
	expr a00 = to_expr(c, a0);
	expr a11 = to_expr(c, a1);
	cout << a00 << endl ;//<< a11 << endl << " *" << endl;

	Sort bvsort2 = s->make_sort(BV, 8);
	Term bvterm2 = s->make_term("x", bvsort2);
	Term aext = s->make_term(Op(Extract, 3, 0), bvterm2);
	cout << "! ! ! ! ! ! ! ! ! ! ! " << aext << endl;

	Term bv2nat = s->make_term(Op(BV_To_Nat), bvterm);
	Term int2bv = s->make_term(Op(Int_To_BV, 8), intterm);

	cout << bv2nat << endl;
	cout << int2bv << endl;

	Z3_ast zbv1 = Z3_mk_zero_ext(c, 1, bv_const_test);
	cout << to_expr(c, zbv1) << endl;


	Term ext2 = s->make_term(Op(Zero_Extend, 1), bvterm);
	cout << ext2 << endl;

	Sort functionsort2 = s->make_sort(FUNCTION, SortVec{ boolsort1, intsort1 } );
	Sort functionsort3 = s->make_sort(FUNCTION, SortVec{ boolsort1, intsort1, boolsort1 } );
	cout << "function exploration: " << endl;
	cout << functionsort << endl;
	Term funfun = s->make_symbol("hellooo", functionsort);
	Term funfun2 = s->make_symbol("hellooo2", functionsort2);
	Term funfun3 = s->make_symbol("hellooo3", functionsort3);
	cout << ":)" << endl << funfun << endl;

	Term appfun = s->make_term(Op(Apply), TermVec{ funfun, boolterm1, intterm, realterm });
	Term appfun2 = s->make_term(Op(Apply), funfun2, boolterm1 );
	Term appfun3 = s->make_term(Op(Apply), funfun3, boolterm1, intterm );
	cout << appfun << endl;
	cout << appfun2 << endl;
	cout << appfun3 << endl;

	cout << " * * * " << endl;
	TermVec ts = { intterm, bvterm };
	print_vec("ts", ts);
	std::vector<Term> t2;
	t2.reserve(ts.size() - 1);
	Term t = ts.back();
	ts.pop_back();
	print_vec("ts later", ts);

	Term x = s->make_symbol("x", boolsort1);
	Term y = s->make_symbol("y", boolsort1);
	Term impx = s->make_term(Implies, x, y);
	cout << x << endl;
	cout << y << endl;
	cout << impx << endl;

	cout << "*" << endl;
	Term qterm =  s->make_term(Forall, TermVec{ x, impx });
	cout << qterm << endl;

	cout << "hash: " << x->hash() << endl;
	cout << "id: " << x->get_id() << endl;

	cout << "**" << endl;

	return 0;
}
