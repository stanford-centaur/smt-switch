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
  s->set_opt("produce-models", true);

  Sort bvsort4 = s->make_sort(BV, 4);
  Sort bvsort8 = s->make_sort(BV, 8);
  Sort arrsort = s->make_sort(ARRAY, bvsort4, bvsort8);

  Term idx0 = s->make_term("idx0", bvsort4);
  Term idx1 = s->make_term("idx1", bvsort4);
  Term val = s->make_term("val", bvsort8);
  Term zero = s->make_value(0, bvsort8);
  Term const_arr = s->make_value(Const_Array, zero, arrsort);
  Term wrarr = s->make_term(Store, const_arr, idx0, val);

  Term constraint = s->make_term(
      And,
      s->make_term(Distinct, s->make_term(Select, wrarr, idx1), zero),
      s->make_term(Distinct, idx0, idx1));
  s->assert_formula(constraint);
  Result r = s->check_sat();
  cout << r << endl;
  assert(r.is_unsat());
}
