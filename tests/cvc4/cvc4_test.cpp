#include <iostream>

#include "smt.h"
#include "cvc4_factory.h"

#include "api/cvc4cpp.h"

using namespace std;
using namespace smt;

int main()
{
  SmtSolver s = CVC4SolverFactory::create();
  Term x = s->declare_const("x", s->make_sort(BV, 8));
  Term y = s->declare_const("y", s->make_sort(BV, 8));
  cout << x->to_string() << endl;
  cout << y->to_string() << endl;
  Term xpy = s->apply(BVAdd, x, y);
  cout << xpy->to_string() << endl;
  Term xext = s->apply(Op(Extract, 3, 0), x);
  cout << xext << endl;
  return 0;
}
