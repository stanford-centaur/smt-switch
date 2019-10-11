#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "cvc4_factory.h"
#include "smt.h"
// after full installation
// #include "smt-switch/cvc4_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

int main()
{
  SmtSolver s = CVC4SolverFactory::create();
  s->set_logic("QF_BV");
  s->set_opt("produce-models", "true");
  s->set_opt("incremental", "true");

  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->make_term("x", bvsort8);
  Term y = s->make_term("y", bvsort8);
  Term z = s->make_term("z", bvsort8);

  Term a = s->make_term(Equal, z, s->make_term(BVAdd, y, z));
  Term b = s->make_term(Equal, z, s->make_term(BVSub, y, z));
  s->assert_formula(a);
  s->assert_formula(b);

  Result r = s->check_sat();
  assert(r.is_sat());

  Term assumption0 =
      s->make_term(And,
                   s->make_term(Distinct, x, s->make_value(0, bvsort8)),
                   s->make_term(Distinct, y, s->make_value(0, bvsort8)));

  Sort boolsort = s->make_sort(BOOL);
  Term il0 = s->make_term("il0", boolsort);
  s->assert_formula(s->make_term(Implies, il0, assumption0));
  r = s->check_sat_assuming(TermVec{ il0 });

  Term assumption1 = s->make_term(Equal, x, s->make_value(1, bvsort8));
  Term il1 = s->make_term("il1", boolsort);
  s->assert_formula(s->make_term(Implies, il1, assumption1));
  r = s->check_sat_assuming({ il1 });
  assert(r.is_sat());
  assert(s->get_value(x)->to_int() == 1);

  s->push();
  s->assert_formula(assumption0);
  r = s->check_sat();
  assert(r.is_unsat());
  s->pop();

  r = s->check_sat();
  assert(r.is_sat());

  s->reset_assertions();
  s->assert_formula(assumption0);
  r = s->check_sat();
  assert(r.is_sat());

  return 0;
}
