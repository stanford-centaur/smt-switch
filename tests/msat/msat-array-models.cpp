#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "msat_factory.h"
#include "smt.h"
// after a full installation
// #include "smt-switch/msat_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

int main()
{
  SmtSolver s = MsatSolverFactory::create();
  s->set_opt("produce-models", "true");
  Sort bvsort32 = s->make_sort(BV, 32);
  Sort array32_32 = s->make_sort(ARRAY, bvsort32, bvsort32);
  Term x0 = s->make_symbol("x0", bvsort32);
  Term x1 = s->make_symbol("x1", bvsort32);
  Term y = s->make_symbol("y", bvsort32);
  Term arr = s->make_symbol("arr", array32_32);

  Term constraint = s->make_term(Equal, s->make_term(Select, arr, x0), x1);
  constraint = s->make_term(
      And, constraint, s->make_term(Equal, s->make_term(Select, arr, x1), y));
  constraint = s->make_term(And, constraint, s->make_term(Distinct, x1, y));
  s->assert_formula(constraint);
  Result r = s->check_sat();

  assert(r.is_sat());

  Term arr_val = s->get_value(arr);

  cout << arr_val << endl;

  return 0;
}
