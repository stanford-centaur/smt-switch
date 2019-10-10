#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "boolector_factory.h"
#include "smt.h"
// after a full installation
// #include "smt-switch/boolector_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

int main()
{
  SmtSolver s = BoolectorSolverFactory::create();
  s->set_logic("QF_ABV");
  s->set_opt("produce-models", "true");

  Sort bvsort4 = s->make_sort(BV, 4);
  Sort bvsort8 = s->make_sort(BV, 8);
  Sort arrsort = s->make_sort(ARRAY, bvsort4, bvsort8);

  Term idx0 = s->make_term("idx0", bvsort4);
  Term idx1 = s->make_term("idx1", bvsort4);
  Term val = s->make_term("val", bvsort8);
  Term zero = s->make_value(0, bvsort8);
  Term const_arr = s->make_value(zero, arrsort);
  assert(!const_arr->is_symbolic_const());
  assert(const_arr->is_value());
  assert(const_arr->get_op() == Const_Array);

  for (auto c : const_arr)
  {
    assert(c == zero);
  }

  Term wrarr = s->make_term(Store, const_arr, idx0, val);
  Term constraint = s->make_term(
      And,
      s->make_term(Distinct, s->make_term(Select, wrarr, idx1), zero),
      s->make_term(Distinct, idx0, idx1));
  s->assert_formula(constraint);
  Result r = s->check_sat();
  cout << r << endl;
  assert(r.is_unsat());

  // test transferring term to a different solver
  SmtSolver s2 = BoolectorSolverFactory::create();
  s2->set_logic("QF_ABV");
  s2->set_opt("produce-models", "true");
  s2->set_opt("incremental", "true");

  Term const_arr2 = s2->transfer_term(const_arr);
  assert(!const_arr2->is_symbolic_const());
  assert(const_arr2->is_value());
  assert(const_arr2->get_op() == Const_Array);

  for (auto c : const_arr2)
  {
    assert(c == s2->transfer_term(zero));
  }

  // this solver has no assertions yet
  assert(s2->check_sat().is_sat());
  Term arr = s2->make_term("arr", arrsort);
  Term arr2 = s2->make_term("arr2", arrsort);
  Term constraint2 = s2->make_term(
      And,
      s2->make_term(Equal, arr, const_arr2),
      s2->make_term(Distinct,
                    s2->make_term(Select, arr, s2->transfer_term(idx0)),
                    s2->transfer_term(zero)));

  // test substitution
  Term t = s2->substitute(constraint2, UnorderedTermMap{ { arr, arr2 } });
  // s2->assert_formula(s2->substitute(constraint2, UnorderedTermMap{{arr,
  // arr2}}));
  // assert(s2->check_sat().is_unsat());

  return 0;
}
