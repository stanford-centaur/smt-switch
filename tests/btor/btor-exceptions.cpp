#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "smt-switch/boolector_factory.h"
#include "smt-switch/smt.h"

using namespace smt;
using namespace std;

int main()
{
  SmtSolver s = BoolectorSolverFactory::create();
  s->set_opt("produce-models", true);

  try
  {
    s->set_logic("QF_NIA");
  }
  catch(SmtException & e)
  {
    cout << e.what() << endl;
  }

  try
  {
    Sort intsort = s->make_sort(INT);
  }
  catch(SmtException & e)
  {
    cout << e.what() << endl;
  }

  Sort bvsort4 = s->make_sort(BV, 4);
  Term x = s->declare_const("x", bvsort4);
  Term y = s->declare_const("y", bvsort4);

  try
  {
    s->assert_formula(s->apply(Ge, x, y));
  }
  catch(SmtException & e)
  {
    cout << e.what() << endl;
  }
  return 0;
}
