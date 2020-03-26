#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

class UnitPrintTests : public ::testing::Test,
                       public testing::WithParamInterface<SolverEnum>
{
 protected:
  void SetUp() override
  {
    s = available_solvers().at(GetParam())();

    bvsort = s->make_sort(BV, 4);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort });
  }
  SmtSolver s;
  Sort bvsort, funsort;
};

TEST_P(UnitPrintTests, SortKind)
{
  ASSERT_EQ(smt::to_string(ARRAY), "ARRAY");
  ASSERT_EQ(smt::to_string(BOOL), "BOOL");
  ASSERT_EQ(smt::to_string(BV), "BV");
  ASSERT_EQ(smt::to_string(INT), "INT");
  ASSERT_EQ(smt::to_string(REAL), "REAL");
  ASSERT_EQ(smt::to_string(FUNCTION), "FUNCTION");
}

TEST_P(UnitPrintTests, Sort) { ASSERT_EQ(bvsort->to_string(), "(_ BitVec 4)"); }

TEST_P(UnitPrintTests, Result)
{
  Result sat(SAT);
  Result unsat(UNSAT);
  Result unknown(UNKNOWN);
  ASSERT_EQ(sat.to_string(), "sat");
  ASSERT_EQ(unsat.to_string(), "unsat");
  ASSERT_EQ(unknown.to_string(), "unknown");
}

TEST_P(UnitPrintTests, Op)
{
  ASSERT_EQ(smt::to_string(BVAdd), "bvadd");
  ASSERT_EQ(smt::to_string(Implies), "=>");
  ASSERT_EQ(smt::to_string(Plus), "+");
  ASSERT_EQ(Op(Extract, 4, 0).to_string(), "(_ extract 4 0)");
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverPringUnit,
                         UnitPrintTests,
                         testing::ValuesIn(available_solver_enums()));

}  // namespace smt_tests
