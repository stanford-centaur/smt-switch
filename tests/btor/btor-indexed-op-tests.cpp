#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "smt.h"

using namespace smt;
using namespace std;

int main()
{
  SmtSolver s = create_solver(BOOLECTOR);
  s->set_opt("produce-models", true);
  Sort bvsort9 = s->make_sort(BV, 9);
  Term x = s->declare_const("x", bvsort9);
  Term y = s->declare_const("y", bvsort9);
  Term onebit = s->declare_const("onebit", s->make_sort(BV, 1));

  Term unnecessary_rotation = s->apply(Op(Rotate_Right, 1), onebit);

  Op ext74 = Op(Extract, 7, 4);
  Term x_upper = s->apply(ext74, x);

  // Op is the the generic object,
  // Fun is something solver specific
  Fun f = x_upper->get_fun();
  assert(f->is_op());
  // but you can always recover the Op if you want to
  // examine it
  assert(f->get_op() == ext74);

  cout << "Op: " << f->get_op() << endl;

  Term y_ror = s->apply(Op(Rotate_Right, 2), y);
  Term y_rol = s->apply(Op(Rotate_Left, 2), y);

  s->assert_formula(s->apply(Equal, y_ror, y_rol));
  s->assert_formula(s->apply(Distinct, y, s->make_const(0, bvsort9)));
  s->assert_formula(s->apply(
      Equal, x, s->apply(Op(Repeat, 9), unnecessary_rotation)));

  assert(s->check_sat());

  Term xc = s->get_value(x);
  Term x_upperc = s->get_value(x_upper);
  Term yc = s->get_value(y);

  cout << "Results:" << endl;
  cout << "\tx = " << xc->as_bitstr() << endl;
  cout << "\tx[7:4] = " << x_upperc->as_bitstr() << endl;
  cout << "\ty = " << yc->as_bitstr() << endl;
  return 0;
}
