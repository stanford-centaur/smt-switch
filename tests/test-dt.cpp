#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

class DTTests : public ::testing::Test,
                 public ::testing::WithParamInterface<SolverEnum>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");
    intsort = s->make_sort(INT);
  }
  SmtSolver s;
  Sort intsort;
};

TEST_P(DTTests, Apply_Constructor)
{

    Term five = s->make_term(5, intsort);

    // Can do things with datatypes after impleementations are provided

    Result res=s->check_sat();

    ASSERT_TRUE(res.is_sat());
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverDTTests,
                         DTTests,
                         testing::ValuesIn(filter_solver_enums({ THEORY_DATATYPE })));

}
