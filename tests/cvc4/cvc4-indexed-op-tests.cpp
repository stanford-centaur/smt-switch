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
  Sort bvsort9 = s->make_sort(BV, 9);
  Term x = s->make_term("x", bvsort9);
  Term y = s->make_term("y", bvsort9);
  Term onebit = s->make_term("onebit", s->make_sort(BV, 1));

  Term unnecessary_rotation = s->make_term(Op(Rotate_Right, 1), onebit);

  Op ext74 = Op(Extract, 7, 4);
  Term x_upper = s->make_term(ext74, x);

  // Op is the the generic object,

  try
  {
    // Fun is something solver specific
    Fun f = x_upper->get_fun();
    assert(f->is_op());
    // but you can always recover the Op if you want to
    // examine it
    assert(f->get_op() == ext74);

    cout << "Op: " << f->get_op() << endl;
  }
  catch (const NotImplementedException & e)
  {
    cout << e.what() << endl;
  }

  Term y_ror = s->make_term(Op(Rotate_Right, 2), y);
  Term y_rol = s->make_term(Op(Rotate_Left, 2), y);

  s->assert_formula(s->make_term(Equal, y_ror, y_rol));
  s->assert_formula(s->make_term(Distinct, y, s->make_value(0, bvsort9)));
  s->assert_formula(
      s->make_term(Equal, x, s->make_term(Op(Repeat, 9), unnecessary_rotation)));

  assert(s->check_sat().is_sat());

  Term xc = s->get_value(x);
  Term x_upperc = s->get_value(x_upper);
  Term yc = s->get_value(y);

  cout << "Results:" << endl;
  cout << "\tx = " << xc->to_int() << endl;
  cout << "\tx[7:4] = " << x_upperc->to_int() << endl;
  cout << "\ty = " << yc->to_int() << endl;
  return 0;
}
