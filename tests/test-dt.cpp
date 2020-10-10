/*********************                                                        */
/*! \file test-dt.cpp
** \verbatim
** Top contributors (to current version):
**   Kristopher Brown
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Tests for theory of datatypes.
**
**
**/

#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

class DTTests : public ::testing::Test,
                 public ::testing::WithParamInterface<SolverConfiguration>
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

TEST_P(DTTests, DatatypeDecl)
{
    SolverConfiguration sc = GetParam();
    if (sc.is_logging_solver) {
      return;
    }
    Term five = s->make_term(5, intsort);

    // Make datatype sort
    DatatypeDecl consListSpec = s->make_datatype_decl("list");

    DatatypeConstructorDecl nildecl = s->make_datatype_constructor_decl("nil");
    DatatypeConstructorDecl consdecl = s->make_datatype_constructor_decl("cons");
    s->add_selector(consdecl, "head", s->make_sort(INT));
    s->add_selector_self(consdecl, "tail");
    s->add_constructor(consListSpec, nildecl);
    s->add_constructor(consListSpec, consdecl);
    Sort listsort = s->make_sort(consListSpec);
    Datatype listdt = listsort->get_datatype();
    // Make datatype terms
    Term cons = s->get_constructor(listsort,"cons");
    Term nil = s->get_constructor(listsort,"nil");
    Term head = s->get_selector(listsort, "cons", "head");
    Term tail = s->get_selector(listsort, "cons", "tail");
    Term isNil = s->get_tester(listsort, "nil");

    // Datatype ops
    Term nilterm = s->make_term(Apply_Constructor,nil);
    Term list5 = s->make_term(Apply_Constructor, cons, five, nilterm);
    Term five_again = s->make_term(Apply_Selector, head, list5);

    // Expected booleans
    s->assert_formula(s->make_term(Equal, five, five_again));
    s->assert_formula(s->make_term(Apply_Tester, isNil, nilterm));
    s->assert_formula(s->make_term(
      Not, s->make_term(Apply_Tester, isNil, list5)));

    Result res=s->check_sat();

    ASSERT_TRUE(listdt->get_name()=="list");
    ASSERT_TRUE(listdt->get_num_constructors()==2);
    ASSERT_TRUE(listdt->get_num_selectors("cons")==2);
    ASSERT_TRUE(listdt->get_num_selectors("nil")==0);

    ASSERT_TRUE(res.is_sat());

    // Expected exceptions
    EXPECT_THROW(s->get_constructor(listsort, "kons"), InternalSolverException);
    EXPECT_THROW(s->get_tester(listsort, "head"), InternalSolverException);
    EXPECT_THROW(s->get_selector(listsort, "nil", "head"), InternalSolverException);
    EXPECT_THROW(listdt->get_num_selectors("kons"), InternalSolverException);
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverDTTests,
                         DTTests,
                         testing::ValuesIn(filter_solver_configurations({ THEORY_DATATYPE })));

}
