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
#include "generic_datatype.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(DTTests);
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

TEST_P(DTTests, DeclareSimpleList)
{
  SolverConfiguration sc = GetParam();
  if (sc.is_logging_solver || s->get_solver_enum() == GENERIC_SOLVER)
  {
    return;
  }

  DatatypeDecl listSpec = s->make_datatype_decl("list");
  DatatypeConstructorDecl nildecl = s->make_datatype_constructor_decl("nil");
  DatatypeConstructorDecl consdecl = s->make_datatype_constructor_decl("cons");
  s->add_selector(consdecl, "head", s->make_sort(INT));
  s->add_selector_self(consdecl, "tail");
  s->add_constructor(listSpec, nildecl);
  s->add_constructor(listSpec, consdecl);
  Sort listsort = s->make_sort(listSpec);
}

TEST_P(DTTests, DeclareSimpleListWithForwardRef)
{
  SolverConfiguration sc = GetParam();
  if (sc.is_logging_solver || s->get_solver_enum() == GENERIC_SOLVER)
  {
    return;
  }

  DatatypeDecl listSpec = s->make_datatype_decl("list");
  DatatypeConstructorDecl nildecl = s->make_datatype_constructor_decl("nil");
  DatatypeConstructorDecl consdecl = s->make_datatype_constructor_decl("cons");
  s->add_selector(consdecl, "head", s->make_sort(INT));
  s->add_constructor(listSpec, nildecl);
  s->add_constructor(listSpec, consdecl);
  Sort listsort = s->make_datatype_sort(listSpec);
  s->add_selector(consdecl, "tail", listsort);
}

TEST_P(DTTests, DatatypeDecl)
{
    SolverConfiguration sc = GetParam();
    if (sc.is_logging_solver) {
      return;
    }

    // Make datatype sort
    DatatypeDecl consListSpec = s->make_datatype_decl("list");

    auto dt_decltest = make_shared<GenericDatatypeDecl>("secondtestdt");

    std::shared_ptr<GenericDatatype> gdt =
        make_shared<GenericDatatype>(dt_decltest);
    assert(gdt->get_num_constructors() == 0);

    shared_ptr<GenericDatatypeConstructorDecl> cons2test =
        shared_ptr<GenericDatatypeConstructorDecl>(
            new GenericDatatypeConstructorDecl("constest"));
    gdt->add_constructor(cons2test);
    assert(gdt->get_num_constructors() == 1);
    assert(gdt->get_num_selectors("constest") == 0);
    assert(gdt->get_name() == "secondtestdt");

    DatatypeConstructorDecl nildecl = s->make_datatype_constructor_decl("nil");
    DatatypeConstructorDecl consdecl = s->make_datatype_constructor_decl("cons");

    shared_ptr<GenericDatatypeConstructorDecl> consdeclgen =
        static_pointer_cast<GenericDatatypeConstructorDecl>(consdecl);
    DatatypeConstructorDecl cons_copy = consdecl;
    ASSERT_EQ(cons_copy, consdecl);

    s->add_selector(consdecl, "head", s->make_sort(INT));
    s->add_constructor(consListSpec, nildecl);
    s->add_constructor(consListSpec, consdecl);

    s->add_selector_self(consdecl, "tail");
    Sort listsort = s->make_sort(consListSpec);

    DatatypeDecl counterdecl = s->make_datatype_decl("counter");
    DatatypeConstructorDecl countercons =
        s->make_datatype_constructor_decl("countercons");
    s->add_constructor(counterdecl, countercons);

    DatatypeConstructorDecl nonAddCons =
        s->make_datatype_constructor_decl("nonAddCons");
    shared_ptr<SelectorComponents> newSelector =
        make_shared<SelectorComponents>();
    newSelector->name = "nonaddselector";
    newSelector->sort = s->make_sort(INT);
    shared_ptr<GenericDatatype> nonAddDT =
        make_shared<GenericDatatype>(consListSpec);
    EXPECT_THROW(nonAddDT->add_selector(nonAddCons, *newSelector),
                 InternalSolverException);

    Sort countersort = s->make_sort(counterdecl);

    assert(countersort->get_sort_kind() == DATATYPE);
    assert(listsort->get_sort_kind() == DATATYPE);
    assert(countersort != listsort);

    Datatype listdt = listsort->get_datatype();

    Term five = s->make_term(5, intsort);
    // Make datatype terms
    Term cons = s->get_constructor(listsort, "cons");
    assert("cons" == cons->to_string());
    Term nil = s->get_constructor(listsort, "nil");

    Term head = s->get_selector(listsort, "cons", "head");

    Term tail = s->get_selector(listsort, "cons", "tail");

    Term isNil = s->get_tester(listsort, "nil");

    // Datatype ops
    Term nilterm = s->make_term(Apply_Constructor, nil);
    Term list5 = s->make_term(Apply_Constructor, cons, five, nilterm);
    Term five_again = s->make_term(Apply_Selector, head, list5);

    // Expected booleans

    s->assert_formula(s->make_term(Equal, five, five_again));

    s->assert_formula(s->make_term(Apply_Tester, isNil, nilterm));

    s->assert_formula(
        s->make_term(Not, s->make_term(Apply_Tester, isNil, list5)));

    Result res = s->check_sat();

    ASSERT_TRUE(listdt->get_name() == "list");
    ASSERT_TRUE(listdt->get_num_constructors() == 2);
    ASSERT_TRUE(listdt->get_num_selectors("cons") == 2);
    ASSERT_TRUE(listdt->get_num_selectors("nil") == 0);

    ASSERT_TRUE(res.is_sat());
    // Expected exceptions

    EXPECT_THROW(s->get_constructor(listsort, "kons"), InternalSolverException);
    EXPECT_THROW(s->get_tester(listsort, "head"), InternalSolverException);
    EXPECT_THROW(listdt->get_num_selectors("kons"), InternalSolverException);
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverDTTests,
                         DTTests,
                         testing::ValuesIn(filter_solver_configurations({ THEORY_DATATYPE })));

}
