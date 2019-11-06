#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "cvc4_factory.h"
#include "smt.h"
// after a full installation
// #include "smt-switch/cvc4_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

int main()
{
  SmtSolver s = CVC4SolverFactory::create();

  // BitVector cases
  Sort bvsort8 = s->make_sort(BV, 8);

  Term four = s->make_term(4, bvsort8);
  Term neg_four = s->make_term(-4, bvsort8);

  assert(neg_four == s->make_term("-4", bvsort8));

  try
  {
    Term impossible = s->make_term("-129", bvsort8);
    assert(false);
  }
  catch (IncorrectUsageException & e)
  {
    cout << e.what() << endl;
  }

  s->push();
  s->assert_formula(
      s->make_term(Not,
                   s->make_term(Equal,
                                s->make_term(BVAdd, four, neg_four),
                                s->make_term(0, bvsort8))));
  Result r = s->check_sat();
  assert(r.is_unsat());
  s->pop();

  r = s->check_sat();
  assert(r.is_sat());

  // Integer cases
  Sort intsort = s->make_sort(INT);
  Term five = s->make_term(5, intsort);
  Term neg_five = s->make_term(-5, intsort);

  assert(neg_five == s->make_term("-5", intsort));

  s->push();
  s->assert_formula(
      s->make_term(Not,
                   s->make_term(Equal,
                                s->make_term(Plus, five, neg_five),
                                s->make_term("0", intsort))));
  r = s->check_sat();
  assert(r.is_unsat());
  s->pop();

  return 0;
}
