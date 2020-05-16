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
    s = create_solver(GetParam());
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
  Term b1 = s->make_symbol("b1", boolsort);
  Term b2 = s->make_symbol("b2", boolsort);
  Term x = s->make_symbol("x", bvsort);

  Term nb2 = s->make_term(Not, b2);
  Term xeq0 = s->make_term(Equal, x, s->make_term(0, bvsort));
  Term nxeq0 = s->make_term(Not, xeq0);
  s->assert_formula(s->make_term(Implies, b1, xeq0));
  s->assert_formula(s->make_term(Implies, nb2, nxeq0));

  ASSERT_THROW(s->check_sat_assuming(TermVec{ xeq0 }), IncorrectUsageException);
  Result r = s->check_sat_assuming(TermVec{ b1, nb2 });
  ASSERT_TRUE(r.is_unsat());
}

INSTANTIATE_TEST_SUITE_P(ParameterizedUnitSolveTests,
                         UnitSolveTests,
                         testing::ValuesIn(filter_solver_enums({ TERMITER })));

}  // namespace smt_tests
