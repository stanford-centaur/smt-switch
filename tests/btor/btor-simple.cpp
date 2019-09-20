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
  Term x = s->make_term("x", bvsort8);
  Term y = s->make_term("y", bvsort8);
  Term xpy = s->make_term(BVAdd, x, y);

  for (auto c : xpy)
  {
    assert(c == x || c == y);
  }

  return 0;
}
