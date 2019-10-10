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
  s->set_opt("produce-models", "true");
  Sort bvsort32 = s->make_sort(BV, 32);
  Sort array32_32 = s->make_sort(ARRAY, bvsort32, bvsort32);
  Term x = s->make_term("x", bvsort32);
  Term y = s->make_term("y", bvsort32);
  Term arr = s->make_term("arr", array32_32);

  cout << "Sorts:" << endl;
  cout << "\tbvsort32 : " << bvsort32 << endl;
  cout << "\tarray32_32 : " << array32_32 << endl;
  s->assert_formula(
      s->make_term(Not,
                   s->make_term(Implies,
                                s->make_term(Equal, x, y),
                                s->make_term(Equal,
                                             s->make_term(Select, arr, x),
                                             s->make_term(Select, arr, y)))));
  assert(!s->check_sat().is_sat());
  return 0;
}
