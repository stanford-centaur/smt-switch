#include <iostream>

#include "assert.h"
#include "smt.h"
#include "z3_factory.h"
#include "z3_sort.h"

using namespace smt;
using namespace std;
// using namespace z3;

int main()
{
  SmtSolver s = Z3SolverFactory::create(false);

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

  Sort functionsort = s->make_sort(
      FUNCTION, SortVec{ boolsort1, intsort1, realsort1, boolsort1 });
  cout << functionsort << endl;

  DatatypeDecl listSpec = s->make_datatype_decl("list");
  DatatypeConstructorDecl nildecl = s->make_datatype_constructor_decl("nil");
  DatatypeConstructorDecl consdecl = s->make_datatype_constructor_decl("cons");
  s->add_selector(consdecl, "head", s->make_sort(INT));
  s->add_selector_self(consdecl, "tail");
  s->add_constructor(listSpec, nildecl);
  s->add_constructor(listSpec, consdecl);
  Sort listsort = s->make_sort(listSpec);
  z3::sort sort = std::static_pointer_cast<Z3Sort>(listsort)->get_z3_type();
  cout << sort << endl
       << sort.constructors() << endl
       << sort.recognizers() << endl;
  cout << "* * * end sort testing * * *" << endl
       << "* * * basic term testing * * *" << endl;

  Term boolterm1 = s->make_term(true);
  Term boolterm2 = s->make_term(false);
  cout << boolterm1 << endl;
  cout << boolterm2 << endl;

  Term intterm = s->make_term(1, intsort1);
  Term realterm = s->make_term(2, realsort1);
  Term bvterm = s->make_term(16, bvsort);
  cout << intterm << endl;
  cout << realterm << endl;
  cout << bvterm << endl;

  cout << "to int:" << endl;
  cout << intterm->to_int() << endl;
  cout << realterm->to_int() << endl;
  cout << bvterm->to_int() << endl;

  cout << "* * * end basic term testing * * *" << endl
       << "* * * op term testing * * *" << endl;

  Term notBool = s->make_term(Not, boolterm1);
  Term isInt = s->make_term(Is_Int, intterm);
  cout << notBool << endl;
  cout << isInt << endl;

  Term impl = s->make_term(Implies, boolterm1, boolterm1);
  Term andBool = s->make_term(And, boolterm1, boolterm2);
  Term concat = s->make_term(Concat, bvterm, bvterm);
  cout << impl << endl;
  cout << andBool << endl;
  cout << concat << endl;

  Sort bvsort2 = s->make_sort(BV, 8);
  Term bvterm2 = s->make_symbol("bvterm2", bvsort2);
  Term aext = s->make_term(Op(Extract, 3, 0), bvterm2);
  cout << aext << endl;

  Term bv2nat = s->make_term(Op(BV_To_Nat), bvterm);
  Term int2bv = s->make_term(Op(Int_To_BV, 8), intterm);
  cout << bv2nat << endl;
  cout << int2bv << endl;

  Term ext2 = s->make_term(Op(Zero_Extend, 1), bvterm);
  cout << ext2 << endl;

  Sort functionsort2 = s->make_sort(FUNCTION, SortVec{ boolsort1, intsort1 });
  Sort functionsort3 =
      s->make_sort(FUNCTION, SortVec{ boolsort1, intsort1, boolsort1 });
  cout << "function exploration: " << endl;
  cout << functionsort << endl;
  Term funfun = s->make_symbol("hellooo", functionsort);
  Term funfun2 = s->make_symbol("hellooo2", functionsort2);
  Term funfun3 = s->make_symbol("hellooo3", functionsort3);
  cout << funfun << endl;

  Term appfun =
      s->make_term(Op(Apply), TermVec{ funfun, boolterm1, intterm, realterm });
  Term appfun2 = s->make_term(Op(Apply), funfun2, boolterm1);
  Term appfun3 = s->make_term(Op(Apply), funfun3, boolterm1, intterm);
  cout << appfun << endl;
  cout << appfun2 << endl;
  cout << appfun3 << endl;

  Term x = s->make_symbol("x", boolsort1);
  Term y = s->make_symbol("y", boolsort1);
  Term impx = s->make_term(Implies, x, y);
  Term qterm = s->make_term(Forall, TermVec{ x, impx });
  Term eterm = s->make_term(Exists, TermVec{ x, impx });
  cout << qterm << endl << eterm << endl;

  cout << "* * * end op term testing * * *" << endl
       << "testing done :)" << endl;

  return 0;
}
