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
  Sort forward_ref_listsort = s->make_sort("list", 0);
  DatatypeConstructorDecl nildecl = s->make_datatype_constructor_decl("nil");
  DatatypeConstructorDecl consdecl = s->make_datatype_constructor_decl("cons");
  s->add_selector(consdecl, "head", s->make_sort(INT));
  s->add_selector(consdecl, "tail", forward_ref_listsort);
  s->add_constructor(listSpec, nildecl);
  s->add_constructor(listSpec, consdecl);
  Sort listsort = s->make_datatype_sort(listSpec, forward_ref_listsort);
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
    EXPECT_THROW(s->get_selector(listsort, "nil", "head"),
                 InternalSolverException);
    EXPECT_THROW(listdt->get_num_selectors("kons"), InternalSolverException);
}

  TEST_P(DTTests, param_datatypes)
  {
    // in future, we should have a better parameterization
    // I can help with that, but for now this would work
    SolverConfiguration sc = GetParam();
    if (sc.solver_enum != GENERIC_SOLVER)
      {
	return;
      }
    if (sc.is_logging_solver) {
      return;
      
    }

    DatatypeDecl pair_decl = s->make_datatype_decl("Pair");
    DatatypeConstructorDecl pair_cons = s->make_datatype_constructor_decl("pair");
    s->add_selector(pair_cons, "first", s->make_sort(PARAM, make_generic_param_sort("X")));
    s->add_selector(pair_cons, "second", s->make_sort(PARAM, make_generic_param_sort("Y")));
    s->add_constructor(pair_decl, pair_cons);
    Sort pairSort = s->make_sort(pair_decl);

    DatatypeDecl par_list = s->make_datatype_decl("List");
    DatatypeConstructorDecl par_nil = s->make_datatype_constructor_decl("nil");
    DatatypeConstructorDecl par_cons = s->make_datatype_constructor_decl("cons");
    s->add_selector(par_cons, "car", s->make_sort(PARAM, make_generic_param_sort("T")));
    s->add_constructor(par_list, par_nil);
    s->add_constructor(par_list, par_cons);
    s->add_selector_self(par_cons, "cdr");
    Sort par_sort = s->make_sort(par_list);

    std::unordered_set<Sort> unresTypes;
    DatatypeDecl tree = s->make_datatype_decl("Tree");
    DatatypeDecl tree_list = s->make_datatype_decl("TreeList");
    DatatypeConstructorDecl empty_cons = s->make_datatype_constructor_decl("empty");
    s->add_constructor(tree_list, empty_cons);
    DatatypeConstructorDecl node_cons = s->make_datatype_constructor_decl("node");
    Sort tree_sort = s->make_sort(UNRESOLVED, make_generic_unresolved_sort(tree));
    Sort tree_list_sort_X = s->make_sort(UNRESOLVED, make_generic_unresolved_sort(tree_list));
    Sort tree_list_sort_Y = s->make_sort(UNRESOLVED, make_generic_unresolved_sort(tree_list));
    static_pointer_cast<UnresolvedSort>(tree_sort)->insert_param("Y");
    static_pointer_cast<UnresolvedSort>(tree_list_sort_X)->insert_param("X");
    static_pointer_cast<UnresolvedSort>(tree_list_sort_Y)->insert_param("Y");

    unresTypes.insert(tree_sort);
    unresTypes.insert(tree_list_sort_Y);
    s->add_selector(node_cons, "value", s->make_sort(PARAM, make_generic_param_sort("X")));
    s->add_constructor(tree, node_cons);
    s->add_selector(node_cons, "children", tree_list_sort_X);
    DatatypeConstructorDecl insert_cons = s->make_datatype_constructor_decl("insert");

    s->add_constructor(tree_list, insert_cons);
    s->add_selector(insert_cons, "head", tree_sort);
    s->add_selector(insert_cons, "tail", tree_list_sort_Y);
    std::vector<DatatypeDecl> dtdecls;
    dtdecls.push_back(tree);
    dtdecls.push_back(tree_list);
    std::vector<Sort> dtsorts;
    dtsorts = s->make_datatype_sorts(dtdecls, unresTypes);


	 }

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverDTTests,
                         DTTests,
                         testing::ValuesIn(filter_solver_configurations({ THEORY_DATATYPE })));

}
