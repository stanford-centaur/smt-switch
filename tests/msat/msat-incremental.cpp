#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "msat_factory.h"
#include "smt.h"
// after full installation
// #include "smt-switch/cvc4_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

int main()
{
  SmtSolver s = MsatSolverFactory::create();
  s->set_logic("QF_BV");
  s->set_opt("produce-models", "true");
  s->set_opt("incremental", "true");

  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->make_term("x", bvsort8);
  Term y = s->make_term("y", bvsort8);
  Term z = s->make_term("z", bvsort8);

  s->assert_formula(s->make_term(Equal, z, s->make_term(BVAdd, y, z)));
  s->assert_formula(s->make_term(Equal, z, s->make_term(BVSub, y, z)));
  Result r = s->check_sat();
  assert(r.is_sat());

  Term assumption =
      s->make_term(And,
                   s->make_term(Distinct, x, s->make_value(0, bvsort8)),
                   s->make_term(Distinct, y, s->make_value(0, bvsort8)));

  r = s->check_sat_assuming(TermVec{ assumption });
  assert(r.is_unsat());

  r = s->check_sat_assuming(
      { s->make_term(Equal, x, s->make_value(1, bvsort8)) });
  assert(r.is_sat());
  assert(s->get_value(x)->to_int() == 1);

  s->push();
  s->assert_formula(assumption);
  r = s->check_sat();
  assert(r.is_unsat());
  s->pop();

  r = s->check_sat();
  assert(r.is_sat());

  s->reset_assertions();
  s->assert_formula(assumption);
  r = s->check_sat();
  assert(r.is_sat());

  return 0;
}
