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

  Term idx = s->make_term("idx", bvsort4);
  Term zero = s->make_value(0, bvsort8);
  Term const_arr = s->make_value(Const_Array, zero, arrsort);

  Term constraint =
      s->make_term(Distinct, s->make_term(Select, const_arr, idx), zero);
  s->assert_formula(constraint);
  Result r = s->check_sat();
  cout << r << endl;
  assert(r.is_unsat());
}
