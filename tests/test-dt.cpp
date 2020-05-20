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
    s->addSelector(consdecl, "head", s->make_sort(INT));
    s->addSelectorSelf(consdecl, "tail");
    s->addConstructor(consListSpec, nildecl);
    s->addConstructor(consListSpec, consdecl);
    Sort listsort = s->make_sort(consListSpec);

    Term cons = s->get_constructor(listsort,"cons");
    Term nil = s->get_constructor(listsort,"nil");
    Term isNil = s->get_tester(listsort, "nil");
    Term head = s->get_selector(listsort, "cons", "head");
    Term tail = s->get_selector(listsort, "cons", "tail");
    Term nilterm = s->make_term(Apply_Constructor,nil);

    Term list5 = s->make_term(Apply_Constructor, cons, five, nilterm);

    Term five_again = s->make_term(Apply_Selector, head, list5);
    s->assert_formula(s->make_term(Equal, five, five_again));
    s->assert_formula(s->make_term(Apply_Tester, isNil, nilterm));
    s->assert_formula(s->make_term(
      Not, s->make_term(Apply_Tester, isNil, list5)));
    Result res=s->check_sat();

    ASSERT_TRUE(res.is_sat());
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverDTTests,
                         DTTests,
                         testing::ValuesIn(filter_solver_enums({ THEORY_DATATYPE })));

}
