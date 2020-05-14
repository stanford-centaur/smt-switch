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
    s = create_solver(GetParam());
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
  Result r = s->check_sat_assuming({ a, b, s->make_term(Not, b) });
  ASSERT_TRUE(r.is_unsat());

  TermVec core = s->get_unsat_core();
  ASSERT_TRUE(core.size() > 1);

  // for solvers using assumptions under the hood,
  // make sure they are re-added correctly
  r = s->check_sat();
  ASSERT_TRUE(r.is_sat());
  ASSERT_THROW(core = s->get_unsat_core(), SmtException);
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverUnsatCoreTests,
    UnsatCoreTests,
    testing::ValuesIn(filter_solver_enums({ UNSAT_CORE })));

}  // namespace smt_tests
