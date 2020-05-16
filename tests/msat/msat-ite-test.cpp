#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "msat_factory.h"
#include "smt.h"
// after a full installation
// #include "smt-switch/boolector_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

int main()
{
  SmtSolver s = MsatSolverFactory::create(false);
  s->set_logic("QF_ABV");
  s->set_opt("produce-models", "true");
  Sort boolsort = s->make_sort(BOOL);
  Term a = s->make_symbol("a", boolsort);
  Term b = s->make_symbol("b", boolsort);
  Term c = s->make_symbol("c", boolsort);

  Sort intsort = s->make_sort(INT);
  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);

  Term ite_bool = s->make_term(Ite, a, b, c);
  Term ite_axiom = s->make_term(
      And,
      s->make_term(Implies, a, s->make_term(Equal, ite_bool, b)),
      s->make_term(
          Implies, s->make_term(Not, a), s->make_term(Equal, ite_bool, c)));

  s->push();
  s->assert_formula(s->make_term(Not, ite_axiom));
  Result r = s->check_sat();
  assert(r.is_unsat());
  s->pop();

  r = s->check_sat();
  assert(r.is_sat());

  Term ite_int = s->make_term(Ite, a, x, y);
  Term ite_axiom_int = s->make_term(
      And,
      s->make_term(Implies, a, s->make_term(Equal, ite_int, x)),
      s->make_term(
          Implies, s->make_term(Not, a), s->make_term(Equal, ite_int, y)));

  s->push();
  s->assert_formula(s->make_term(Not, ite_axiom_int));
  r = s->check_sat();
  assert(r.is_unsat());
  s->pop();

  return 0;
}
