#include "assert.h"
#include <iostream>
#include <string>

#include "smt.h"

using namespace smt;
using namespace std;

int main()
{
  unsigned int NUM_TERMS=20;

  SmtSolver s = create_solver(BOOLECTOR);
  s->set_opt("produce-models", true);
  Sort bvsort8 = s->make_sort(BV, 8);

  TermVec v;
  v.reserve(NUM_TERMS);
  for(size_t i=0; i < NUM_TERMS; ++i)
  {
    string name = "x" + to_string(i);
    v.push_back(s->declare_const(name, bvsort8));
  }

  Term trailing = v[0];
  for(size_t i=1; i < NUM_TERMS; ++i)
  {
    s->assert_formula(s->apply_func(EQUAL,
                                    v[i],
                                    s->apply_func(BVADD, trailing, s->make_const(1, bvsort8))
                                    )
                      );
    trailing = v[i];
  }
  s->assert_formula(s->apply_func(EQUAL, v[0], s->make_const(1, bvsort8)));
  bool res = s->check_sat();
  assert(res);

  // FIXME: There's a memory leak here related to get_value
  //        can't figure it out...might be in boolector itself
  for(size_t i=0; i < NUM_TERMS; ++i)
  {
    cout << "\t x" << i << " = " << s->get_value(v[i])->as_bitstr() << endl;
  }
  return 0;
}
