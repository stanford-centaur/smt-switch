#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "msat_factory.h"
#include "smt.h"
// after a full installation
// #include "smt-switch/msat_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

int main()
{
  SmtSolver s = MsatSolverFactory::create_interpolating_solver();
  Sort intsort = s->make_sort(INT);

  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term z = s->make_symbol("z", intsort);

  try
  {
    s->assert_formula(s->make_term(Equal, x, s->make_value(0, intsort)));
  }
  catch (IncorrectUsageException & e)
  {
    cout << e.what() << endl;
  }

  Term A = s->make_term(And, s->make_term(Lt, x, y), s->make_term(Lt, y, z));
  Term B = s->make_term(Gt, x, z);
  Term I;
  bool got_interpolant = s->get_interpolant(A, B, I);

  if (got_interpolant)
  {
    cout << "Found interpolant: " << I << endl;
  }
  else
  {
    cout << "Didn't find an interpolant..." << endl;
    assert(false);
  }

  // try getting a second interpolant with different A and B
  A = s->make_term(And, s->make_term(Gt, x, y), s->make_term(Gt, y, z));
  B = s->make_term(Lt, x, z);
  got_interpolant = s->get_interpolant(A, B, I);

  if (got_interpolant)
  {
    cout << "Found interpolant: " << I << endl;
  }
  else
  {
    cout << "Didn't find an interpolant..." << endl;
    assert(false);
  }

  // now try a satisfiable formula
  got_interpolant = s->get_interpolant(A, s->make_term(Gt, x, z), I);
  assert(!got_interpolant);

  return 0;
}
