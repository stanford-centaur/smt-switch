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
  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->declare_const("x", bvsort8);
  Term y = s->declare_const("y", bvsort8);
  Term z = s->declare_const("z", bvsort8);
  Term _true = s->make_const(true);
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

  Term xpy = s->apply(BVAdd, x, y);
  Term z_eq_xpy = s->apply(Equal, z, xpy);

  assert(x->is_symbolic_const());
  assert(!xpy->is_symbolic_const());

  Fun f = z_eq_xpy->get_fun();
  assert(f->is_op());
  assert(f->get_op().prim_op == Equal);

  Op ext30 = Op(Extract, 3, 0);
  Term x_lower = s->apply(ext30, x);
  Term x_ext = s->apply(Op(Zero_Extend, 4), x_lower);

  Fun uf = s->declare_fun(
      "f", std::vector<Sort>{ x_lower->get_sort() }, x->get_sort());
  Term uf_app = s->apply(uf, x_lower);

  s->assert_formula(z_eq_xpy);
  s->assert_formula(s->apply(BVUlt, x, s->make_const(4, bvsort8)));
  s->assert_formula(s->apply(BVUlt, y, s->make_const(4, bvsort8)));
  s->assert_formula(s->apply(BVUgt, z, s->make_const("5", bvsort8)));
  // This is actually a redundant assertion -- just testing
  s->assert_formula(s->apply(Equal, x_ext, x));
  s->assert_formula(s->apply(Distinct, x, z));
  s->assert_formula(s->apply(BVUle, uf_app, s->make_const(3, bvsort8)));
  s->assert_formula(s->apply(BVUge, uf_app, s->make_const(3, bvsort8)));
  assert(s->check_sat().is_sat());

  Term xc = s->get_value(x);
  Term yc = s->get_value(y);
  Term zc = s->get_value(z);
  Term x_extc = s->get_value(x_ext);
  Term x_lowerc = s->get_value(x_lower);
  Term uf_appc = s->get_value(uf_app);

  cout << "Got the following values:" << endl;
  cout << "\txc = " << xc->to_int() << endl;
  cout << "\tyc = " << yc->to_int() << endl;
  cout << "\tzc = " << zc->to_int() << endl;
  cout << "\tx[3:0] = " << x_lowerc->to_int() << endl;
  cout << "\t((_ zero_extend 4) x[3:0]) = " << x_extc->to_int() << endl;
  cout << "\tf(x[3:0]) = " << uf_appc->to_int() << endl;
  return 0;
}
