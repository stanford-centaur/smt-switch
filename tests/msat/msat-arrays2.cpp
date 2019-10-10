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
  Sort bvsort4 = s->make_sort(BV, 4);
  Sort bvsort8 = s->make_sort(BV, 8);
  Sort array4_8 = s->make_sort(ARRAY, bvsort4, bvsort8);
  Term x = s->make_term("x", bvsort4);
  Term elem = s->make_term("elem", bvsort8);
  Term mem = s->make_term("mem", array4_8);

  Term new_array = s->make_term(Store, mem, x, elem);
  assert(new_array->get_op() == Store);

  for (auto c : new_array)
  {
    cout << c << endl;
  }

  return 0;
}
