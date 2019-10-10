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

  // Ideally, wouldn't pollute the rest of the space
  // Result r = s->check_sat();
  // cout << r << endl;
  // assert(r.is_sat());

  return 0;
}
