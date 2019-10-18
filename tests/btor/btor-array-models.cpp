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
  std::cout << "entering main" << std::endl;
  SmtSolver s = BoolectorSolverFactory::create();
  s->set_opt("produce-models", "true");
  Sort bvsort32 = s->make_sort(BV, 32);
  Sort array32_32 = s->make_sort(ARRAY, bvsort32, bvsort32);
  Term x0 = s->make_term("x0", bvsort32);
  Term x1 = s->make_term("x1", bvsort32);
  Term y = s->make_term("y", bvsort32);
  Term arr = s->make_term("arr", array32_32);

  std::cout << "after creating symbols" << std::endl;

  Term constraint = s->make_term(Equal, s->make_term(Select, arr, x0), x1);
  constraint = s->make_term(
      And, constraint, s->make_term(Equal, s->make_term(Select, arr, x1), y));
  constraint = s->make_term(And, constraint, s->make_term(Distinct, x1, y));

  std::cout << "after creating constraint" << std::endl;

  s->assert_formula(constraint);

  std::cout << "after asserting" << std::endl;

  Result r = s->check_sat();

  std::cout << "after check_sat" << std::endl;

  assert(r.is_sat());

  std::cout << "after assertion" << std::endl;

  Term arr_val = s->get_value(arr);

  cout << arr_val << endl;

  return 0;
}
