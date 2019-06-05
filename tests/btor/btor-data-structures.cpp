#include <iostream>
#include <string>
#include "assert.h"

#include "data_structures.h"

#include "boolector_create.h"

using namespace smt;
using namespace std;

int main()
{
  unsigned int NUM_TERMS = 20;

  SmtSolver s = BoolectorSolverFactory::create();
  s->set_opt("produce-models", true);
  Sort bvsort8 = s->make_sort(BV, 8);

  TermUnorderedMap tum;
  TermVec v;
  v.reserve(NUM_TERMS);
  for (size_t i = 0; i < NUM_TERMS; ++i)
  {
    Term x = s->declare_const("x" + to_string(i), bvsort8);
    Term y = s->declare_const("y" + to_string(i), bvsort8);
    v.push_back(x);
    tum[x] = y;
  }

  Term trailing = v[0];
  for (size_t i = 1; i < NUM_TERMS; ++i)
  {
    s->assert_formula(s->apply(
        Equal, v[i], s->apply(BVAdd, trailing, s->make_const(1, bvsort8))));
    trailing = v[i];
  }
  Term zero = s->make_const(0, bvsort8);
  cout << zero->to_string() << endl;

  Term v0_eq_0 = s->apply(Equal, v[0], zero);
  s->assert_formula(v0_eq_0);

  cout << "Children of term:" << endl;
  // Could use iterators directly:
  //   for (TermIter it = v0_eq_0->begin(); it != v0_eq_0->end(); ++it)
  // Or use a range-based loop
  for (auto c : v0_eq_0)
  {
    cout << "got: " << c << endl;
  }

  // just assign all ys to x counterparts
  for (auto it = tum.begin(); it != tum.end(); ++it)
  {
    std::cout << "assert: " << it->first << " = " << it->second << std::endl;
    s->assert_formula(s->apply(Equal, it->first, it->second));
  }

  bool res = s->check_sat();
  assert(res);

  // can print variable names, but otherwise boolector doesn't maintain strings
  // for expressions
  cout << "Assignments:" << std::endl;
  for (size_t i = 0; i < NUM_TERMS; ++i)
  {
    cout << "\t " << v[i]->to_string() << " = "
         << s->get_value(v[i])->as_bitstr() << endl;
    cout << "\t " << tum.at(v[i])->to_string() << " = "
         << s->get_value(tum.at(v[i]))->as_bitstr() << endl;
  }
  return 0;
}
