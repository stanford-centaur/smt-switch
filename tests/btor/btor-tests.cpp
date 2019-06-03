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
  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->declare_const("x", bvsort8);
  Term y = s->declare_const("y", bvsort8);
  Term z = s->declare_const("z", bvsort8);
  assert(x != y);
  Term x_copy = x;
  assert(x == x_copy);

  // check sorts
  Sort xsort = x->get_sort();
  Sort ysort = y->get_sort();
  assert(xsort == ysort);

  Sort arr_sort = s->make_sort(ARRAY, s->make_sort(BV, 4), bvsort8);
  assert(xsort != arr_sort);
  assert(xsort != arr_sort->get_indexsort());
  assert(xsort == arr_sort->get_elemsort());

  Term xpy = s->apply_func(BVAdd, x, y);
  Term z_eq_xpy = s->apply_func(Equal, z, xpy);

  Func f = z_eq_xpy->get_func();
  assert(f->is_op());
  assert(f->get_op().prim_op == Equal);

  Op ext30 = Op(Extract, 3, 0);

  Term x_lower = s->apply_func(ext30, x);

  s->assert_formula(z_eq_xpy);
  s->assert_formula(s->apply_func(BVUlt, x, s->make_const(4, bvsort8)));
  s->assert_formula(s->apply_func(BVUlt, y, s->make_const(4, bvsort8)));
  s->assert_formula(s->apply_func(BVUgt, z, s->make_const(5, bvsort8)));
  assert(s->check_sat());

  Term xc = s->get_value(x);
  Term yc = s->get_value(y);
  Term zc = s->get_value(z);
  Term x_lowerc = s->get_value(x_lower);

  cout << "Got the following values:" << endl;
  cout << "\txc = " << xc->as_bitstr() << endl;
  cout << "\tyc = " << yc->as_bitstr() << endl;
  cout << "\tzc = " << zc->as_bitstr() << endl;
  cout << "\tx[3:0] = " << x_lowerc->as_bitstr() << endl;
  return 0;
}
