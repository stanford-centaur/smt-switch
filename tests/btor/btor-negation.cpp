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
  // Boolector doesn't have a NOT node
  // instead they just set the LSB of the id/pointer
  // to retrieve the real node, it needs btor_node_real_addr
  // this simple test is to ensure that smt-switch is handling this correctly

  SmtSolver s = BoolectorSolverFactory::create();
  s->set_logic("QF_ABV");
  s->set_opt("produce-models", true);
  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->make_term("x", bvsort8);
  Term five = s->make_value(5, bvsort8);
  Term ult5 = s->make_term(BVUlt, x, five);
  Term nult5 = s->make_term(Not, ult5);

  // Boolector turns everything into bv ops
  assert(nult5->get_op() == BVNot);
  for (auto c : nult5)
  {
    assert(c == ult5);
  }
  assert(s->make_term(Not, nult5) == ult5);
  assert(s->make_term(Not, nult5)->get_op() == BVUlt);
  return 0;
}
