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
  SmtSolver s = MsatSolverFactory::create();
  s->set_opt("interpolation", "true");
  Sort intsort = s->make_sort(INT);

  Term x = s->make_term("x", intsort);
  Term y = s->make_term("y", intsort);
  Term z = s->make_term("z", intsort);

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

  // You can reset the solver if you want to do regular solving
  // but you have to recreate the terms
  // because the original environment is gone
  s->reset();
  s->set_opt("produce-models", "true");
  intsort = s->make_sort(INT);
  x = s->make_term("x", intsort);
  s->assert_formula(s->make_term(Equal, x, s->make_value(0, intsort)));
  Result r = s->check_sat();
  cout << r << endl;
  assert(r.is_sat());

  return 0;
}
