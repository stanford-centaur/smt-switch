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

    DatatypeDecl consListSpec = s->make_datatype_decl("list");

    DatatypeConstructorDecl nildecl = s->make_datatype_constructor_decl("nil");
    DatatypeConstructorDecl consdecl = s->make_datatype_constructor_decl("cons");
    s->add_selector(consdecl, "head", s->make_sort(INT));
    s->add_selector_self(consdecl, "tail");
    s->add_constructor(consListSpec, nildecl);
    s->add_constructor(consListSpec, consdecl);
    Sort listsort = s->make_sort(consListSpec);
    Result res=s->check_sat();

    ASSERT_TRUE(res.is_sat());
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverDTTests,
                         DTTests,
                         testing::ValuesIn(filter_solver_enums({ THEORY_DATATYPE })));

}
