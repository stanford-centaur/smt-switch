#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "cvc4_factory.h"
#include "smt.h"
// after full installation
// #include "smt-switch/cvc4_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

int main()
{
  SmtSolver s = CVC4SolverFactory::create();
  s->set_opt("produce-models", true);
  s->set_logic("QF_NIA");
  Sort intsort = s->make_sort(INT);
  Term x = s->declare_const("x", intsort);
  Term y = s->declare_const("y", intsort);
  Term z = s->declare_const("z", intsort);

  s->assert_formula(s->apply(Ge, x, y));
  s->assert_formula(s->apply(Le, z, s->apply(Plus, x, y)));
  s->assert_formula(s->apply(Lt, s->apply(Negate, z), s->apply(Minus, x, y)));
  s->assert_formula(s->apply(Gt, s->apply(Minus, x, y), s->apply(Mult, x, y)));

  Result r = s->check_sat();
  assert(r.is_sat());

  cout << "Model Values:" << endl;
  for (auto t : std::vector{ x, y, z })
  {
    cout << "\t" << t << " = " << s->get_value(t) << endl;
  }
  return 0;
}
