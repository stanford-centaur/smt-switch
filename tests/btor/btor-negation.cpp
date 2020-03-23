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

void lite_solver_test()
{
  // Boolector doesn't have a NOT node
  // instead they just set the LSB of the id/pointer
  // to retrieve the real node, it needs btor_node_real_addr
  // this simple test is to ensure that smt-switch is handling this correctly

  // creating a solver WITHOUT smt-switch level logging of terms
  SmtSolver s = BoolectorSolverFactory::create_lite_solver();
  s->set_logic("QF_ABV");
  s->set_opt("produce-models", "true");
  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bvsort8);
  Term five = s->make_term(5, bvsort8);
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
}

void logging_solver_test()
{
  // creating a solver WITH smt-switch level logging of terms
  SmtSolver s = BoolectorSolverFactory::create();
  s->set_logic("QF_ABV");
  s->set_opt("produce-models", "true");
  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bvsort8);
  Term five = s->make_term(5, bvsort8);
  Term ult5 = s->make_term(BVUlt, x, five);
  Term nult5 = s->make_term(Not, ult5);

  assert(nult5->get_op() == Not);
  for (auto c : nult5)
  {
    assert(c == ult5);
  }

  // terms no longer rewritten on the fly
  assert(s->make_term(Not, nult5) != ult5);
  assert(s->make_term(Not, nult5)->get_op() == Not);
}

int main()
{
  lite_solver_test();
  logging_solver_test();
  return 0;
}
