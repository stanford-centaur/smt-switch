#include "assert.h"
#include <iostream>
#include <memory>
#include <vector>

#include "smt.h"

using namespace smt;
using namespace std;

int main() {

  Solver s = create_solver(BOOLECTOR);
  s->set_opt("produce-models", true);
  Sort bvsort8 = s->construct_sort(BV, 8);
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

  Sort arr_sort = s->construct_sort(ARRAY, s->construct_sort(BV, 4), bvsort8);
  assert(xsort != arr_sort);
  assert(xsort != arr_sort->get_indexsort());
  assert(xsort == arr_sort->get_elemsort());

  Term xpy = s->apply_func(BVADD, x, y);
  Term z_eq_xpy = s->apply_func(EQUAL, z, xpy);

  Func f = z_eq_xpy->get_func();
  assert(holds_alternative<PrimOp>(f));
  assert(get<PrimOp>(f) == EQUAL);

  s->assert_formula(z_eq_xpy);
  s->assert_formula(s->apply_func(BVULT, x, s->make_const(4, bvsort8)));
  s->assert_formula(s->apply_func(BVULT, y, s->make_const(4, bvsort8)));
  s->assert_formula(s->apply_func(BVUGT, z, s->make_const(5, bvsort8)));
  assert(s->check_sat());

  Term xc = s->get_value(x);
  Term yc = s->get_value(y);
  Term zc = s->get_value(z);

  cout << "Got the following values:" << endl;
  cout << "\t" << xc->as_bitstr() << endl;
  cout << "\t" << yc->as_bitstr() << endl;
  cout << "\t" << zc->as_bitstr() << endl;
  return 0;
}
