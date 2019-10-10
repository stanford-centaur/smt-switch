#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "boolector_factory.h"
#include "smt.h"
// after full installation
// #include "smt-switch/boolector_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

int main()
{
  SmtSolver s = BoolectorSolverFactory::create();
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

  s->push();
  s->assert_formula(assumption);
  r = s->check_sat();
  assert(r.is_unsat());
  s->pop();

  r = s->check_sat();
  assert(r.is_sat());

  try
  {
    s->reset_assertions();
    s->assert_formula(assumption);
    r = s->check_sat();
    assert(r.is_sat());
  }
  catch (NotImplementedException & e)
  {
    cout << e.what() << endl;
  }

  return 0;
}
