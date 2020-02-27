#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;


namespace smt_tests {

UnorderedTermSet get_free_symbols(Term & t)
{
  UnorderedTermSet free_symbols;
  TermVec to_visit({t});
  UnorderedTermSet visited;

  Term n;
  while (to_visit.size())
  {
    n = to_visit.back();
    to_visit.pop_back();

    if (visited.find(n) == visited.end())
    {
      visited.insert(n);
      for (auto nn : n)
      {
        to_visit.push_back(nn);
      }

      if (n->is_symbolic_const())
      {
        free_symbols.insert(n);
      }
    }
  }

  return free_symbols;
}

class ItpTests : public ::testing::Test,
                 public ::testing::WithParamInterface<SolverEnum>
{
protected:
  void SetUp() override
  {
    itp = available_interpolators().at(GetParam())();

    intsort = itp->make_sort(INT);
    x = itp->make_symbol("x", intsort);
    y = itp->make_symbol("y", intsort);
    z = itp->make_symbol("z", intsort);
    w = itp->make_symbol("w", intsort);
  }
  SmtSolver itp;
  Sort intsort;
  Term x, y, z, w;
};

TEST_P(ItpTests, Test_ITP)
{
  Term A = itp->make_term(Lt, x, y);
  A = itp->make_term(And, A, itp->make_term(Lt, y, w));

  Term B = itp->make_term(Gt, z, w);
  B = itp->make_term(And, itp->make_term(Lt, z, x));

  // TODO: finish this
  Term I;
  bool success = itp->get_interpolant(A, B, I);
  ASSERT_TRUE(success);

  UnorderedTermSet free_symbols = get_free_symbols(I);

  ASSERT_TRUE(free_symbols.find(y) == free_symbols.end());
  ASSERT_TRUE(free_symbols.find(z) == free_symbols.end());
}

}
