#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "gmp.h"
#include "yices.h"
#include "yices2_sort.h"
#include "yices2_term.h"

#include "smt.h"
#include "yices2_factory.h"
// after a full installation
// #include "smt-switch/msat_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

void check(Term * constraint, SmtSolver * s)
{
  // cout << "checking constraint.. " << *constraint << endl;

  SmtSolver s2 = Yices2SolverFactory::create();
  s2->set_opt("produce-models", "true");
  s2->set_opt("incremental", "true");

  TermTranslator tt(s2);

  Term constraint2 = tt.transfer_term((*constraint));
  // Term T2 = tt.transfer_term(T);
  // // ensure it can handle transfering again (even though it already built the
  // // node)
  constraint2 = tt.transfer_term((*constraint));
  s2->assert_formula(constraint2);

  cout << "term from solver 1: " << *constraint << endl;
  cout << "term from solver 2: " << constraint2 << endl;

  assert((*s)->check_sat().is_sat());
  assert(s2->check_sat().is_sat());
}

int main()
{
  SmtSolver s = Yices2SolverFactory::create();
  s->set_opt("produce-models", "true");
  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->make_symbol("x", bvsort8);
  Term y = s->make_symbol("y", bvsort8);
  Term z = s->make_symbol("z", bvsort8);

  Term a = s->make_symbol("a", s->make_sort(INT));
  Term b = s->make_symbol("b", s->make_sort(INT));
  Term c = s->make_symbol("c", s->make_sort(INT));

  Term constraint;

  constraint = s->make_term(
      Equal, c, s->make_term(Pow, b, s->make_term("4", s->make_sort(INT))));
  constraint = s->make_term(And, constraint, s->make_term(Lt, a, b));

  check(&constraint, &s);

  constraint = s->make_term(Equal, z, s->make_term(BVMul, x, y));
  constraint = s->make_term(And, constraint, s->make_term(Lt, a, b));

  check(&constraint, &s);

  constraint = s->make_term(Equal, z, s->make_term(BVAdd, x, y));
  constraint = s->make_term(And, constraint, s->make_term(Lt, a, b));

  check(&constraint, &s);

  constraint =
      s->make_term(Equal, z, s->make_term(BVAdd, x, s->make_term(BVMul, y, z)));
  constraint = s->make_term(And, constraint, s->make_term(Lt, a, b));

  check(&constraint, &s);

  constraint =
      s->make_term(Equal, z, s->make_term(BVAdd, x, s->make_term(BVMul, y, z)));
  constraint = s->make_term(
      And,
      constraint,
      s->make_term(Equal,
                   a,
                   s->make_term(Pow, b, s->make_term("4", s->make_sort(INT)))));

  check(&constraint, &s);

  Term bv_sum = s->make_term(BVAdd, x, s->make_term(BVMul, y, z));
  // cout << "bv sum : " << bv_sum << endl;
  constraint = s->make_term(Equal, z, bv_sum);

  c = s->make_term("3", s->make_sort(INT));

  constraint = s->make_term(
      And, constraint, s->make_term(Equal, a, s->make_term(Pow, b, c)));

  check(&constraint, &s);

  Term d = s->make_symbol("d", s->make_sort(INT));

  constraint = s->make_term(
      Equal, s->make_term("100", s->make_sort(INT)), s->make_term(Plus, b, d));

  constraint =
      s->make_term(And,
                   constraint,
                   s->make_term(Ge, b, s->make_term("12", s->make_sort(INT))));

  check(&constraint, &s);

  constraint = s->make_term(
      Equal,
      s->make_term("100", s->make_sort(INT)),
      s->make_term(Plus, b, s->make_term("55", s->make_sort(INT))));

  constraint =
      s->make_term(And,
                   constraint,
                   s->make_term(Ge, b, s->make_term("12", s->make_sort(INT))));

  check(&constraint, &s);

  // non-linear arithmetic warning right now.. 
  //   constraint = s->make_term(
  //       Equal, s->make_term("100", s->make_sort(INT)), s->make_term(Mult, b,
  //       d));

  //   cout << "constraint " << constraint << endl;
  //   constraint = s->make_term(And, constraint, s->make_term(Ge, b,
  //   s->make_term("12", s->make_sort(INT))));

  //   check(&constraint, &s);

  return 0;
}
