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
  s->set_opt("produce-models", true);
  Sort bvsort9 = s->make_sort(BV, 9);
  Term x = s->make_term("x", bvsort9);
  Term y = s->make_term("y", bvsort9);
  Term onebit = s->make_term("onebit", s->make_sort(BV, 1));

  Term unnecessary_rotation = s->make_term(Op(Rotate_Right, 1), onebit);

  Op ext74 = Op(Extract, 7, 4);
  Term x_upper = s->make_term(ext74, x);

  Op op = x_upper->get_op();
  cout << "Op: " << op << endl;

  Term y_ror = s->make_term(Op(Rotate_Right, 2), y);
  Term y_rol = s->make_term(Op(Rotate_Left, 2), y);

  s->assert_formula(s->make_term(Equal, y_ror, y_rol));
  s->assert_formula(s->make_term(Distinct, y, s->make_value(0, bvsort9)));
  s->assert_formula(s->make_term(
      Equal, x, s->make_term(Op(Repeat, 9), unnecessary_rotation)));

  assert(s->check_sat().is_sat());

  Term xc = s->get_value(x);
  Term x_upperc = s->get_value(x_upper);
  Term yc = s->get_value(y);

  cout << "Results:" << endl;
  cout << x << ": " << xc->to_int() << endl;
  cout << x_upper << ": " << x_upperc->to_int() << endl;
  cout << y << ": " << yc->to_int() << endl;
  return 0;
}
