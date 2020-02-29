#include <utility>
#include <vector>

#include "available_solvers.h"
#include "exceptions.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

class UnitSolveTests : public ::testing::Test,
                       public testing::WithParamInterface<SolverEnum>
{
 protected:
  void SetUp() override
  {
    s = available_solvers().at(GetParam())();
    s->set_opt("incremental", "true");
    s->set_opt("produce-models", "true");

    boolsort = s->make_sort(BOOL);
    bvsort = s->make_sort(BV, 4);
  }
  SmtSolver s;
  Sort boolsort, bvsort;
};

TEST_P(UnitSolveTests, CheckSatAssuming)
{
  Term b = s->make_symbol("b", boolsort);
  Term x = s->make_symbol("x", bvsort);

  Term xeq0 = s->make_term(Equal, x, s->make_term(0, bvsort));
  s->assert_formula(s->make_term(Implies, b, xeq0));

  s->assert_formula(s->make_term(Not, xeq0));
  ASSERT_THROW(s->check_sat_assuming(TermVec{ xeq0 }), IncorrectUsageException);
  Result r = s->check_sat_assuming(TermVec{ b });
  ASSERT_TRUE(r.is_unsat());
}

INSTANTIATE_TEST_SUITE_P(ParameterizedUnitSolveTests,
                         UnitSolveTests,
                         testing::ValuesIn(available_solver_enums()));

}  // namespace smt_tests
