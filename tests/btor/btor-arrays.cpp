#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "smt.h"

using namespace smt;
using namespace std;

int main()
{
  SmtSolver s = create_solver(BOOLECTOR);
  s->set_opt("produce-models", true);
  Sort bvsort32 = s->make_sort(BV, 32);
  Sort array32_32 = s->make_sort(ARRAY, bvsort32, bvsort32);
  Term x = s->declare_const("x", bvsort32);
  Term y = s->declare_const("y", bvsort32);
  Term arr = s->declare_const("arr", array32_32);

  cout << "Sorts:" << endl;
  cout << "\tbvsort32 : " << bvsort32 << endl;
  cout << "\tarray32_32 : " << array32_32 << endl;
  s->assert_formula(
                    s->apply(Not,
                    s->apply(Implies,
                                  s->apply(Equal, x, y),
                                  s->apply(Equal,
                                                s->apply(Select, arr, x),
                                                s->apply(Select, arr, y)
                                                )
                                  )
                                  )
  );
  assert(!s->check_sat());
  return 0;
}
