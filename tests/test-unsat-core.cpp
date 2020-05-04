#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

class UnsatCoreTests : public ::testing::Test,
                 public ::testing::WithParamInterface<SolverEnum>
{
 protected:
  void SetUp() override
  {
    s = available_solvers().at(GetParam())();
    s->set_opt("incremental", "true");
    s->set_opt("produce-unsat-cores", "true");
    boolsort = s->make_sort(BOOL);
  }
  SmtSolver s;
  Sort boolsort;
};

TEST_P(UnsatCoreTests, UnsatCore)
{
  Term a = s->make_symbol("a", boolsort);
  Term b = s->make_symbol("b", boolsort);
  s->assert_formula(a);
  s->assert_formula(b);
  s->assert_formula(s->make_term(Not, b));
  Result r = s->check_sat();
  ASSERT_TRUE(r.is_unsat());

  TermVec core = s->get_unsat_core();
  ASSERT_TRUE(core.size() > 1);

  // for solvers using assumptions under the hood,
  // make sure they are re-added correctly
  r = s->check_sat();
  ASSERT_TRUE(r.is_unsat());
  core = s->get_unsat_core();
  ASSERT_TRUE(core.size() > 1);
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverUnsatCoreTests,
                         UnsatCoreTests,
                         testing::ValuesIn(available_unsat_core_solver_enums()));

}  // namespace smt_tests
