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

  try
  {
    s->set_logic("QF_NIA");
  }
  catch (SmtException & e)
  {
    cout << e.what() << endl;
  }

  try
  {
    Sort intsort = s->make_sort(INT);
  }
  catch (SmtException & e)
  {
    cout << e.what() << endl;
  }

  Sort bvsort4 = s->make_sort(BV, 4);
  Term x = s->make_term("x", bvsort4);
  Term y = s->make_term("y", bvsort4);

  try
  {
    s->assert_formula(s->make_term(Ge, x, y));
  }
  catch (SmtException & e)
  {
    cout << e.what() << endl;
  }
  return 0;
}
