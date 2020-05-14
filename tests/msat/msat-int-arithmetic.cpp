#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "msat_factory.h"
#include "smt.h"
// after full installation
// #include "smt-switch/msat_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

int main()
{
  SmtSolver s = MsatSolverFactory::create(false);
  s->set_opt("produce-models", "true");
  s->set_logic("QF_NIA");
  Sort intsort = s->make_sort(INT);
  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term z = s->make_symbol("z", intsort);

  s->assert_formula(s->make_term(Ge, x, y));
  s->assert_formula(s->make_term(Le, z, s->make_term(Plus, x, y)));
  s->assert_formula(
      s->make_term(Lt, s->make_term(Negate, z), s->make_term(Minus, x, y)));
  s->assert_formula(
      s->make_term(Gt, s->make_term(Minus, x, y), s->make_term(Mult, x, y)));

  Result r = s->check_sat();
  assert(r.is_sat());

  cout << "Model Values:" << endl;
  for (auto t : TermVec({ x, y, z }))
  {
    cout << "\t" << t << " = " << s->get_value(t) << endl;
  }
  return 0;
}
