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
using namespace smt_tests;
using namespace std;

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(Datatypes);
class Datatypes : public ::testing::Test,
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

TEST_P(Datatypes, DeclareSimpleList)
{
  if (s->get_solver_enum() == GENERIC_SOLVER)
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

TEST_P(Datatypes, SelectorBelongsToOneConstructor)
{
  DatatypeDecl maybedecl = s->make_datatype_decl("maybe");
  DatatypeConstructorDecl nothing =
      s->make_datatype_constructor_decl("nothing");
  DatatypeConstructorDecl just = s->make_datatype_constructor_decl("just");
  s->add_selector(just, "value", intsort);
  s->add_constructor(maybedecl, nothing);
  s->add_constructor(maybedecl, just);
  Sort maybesort = s->make_sort(maybedecl);

  // "value" belongs to just alone, so asking for nothing's must fail rather
  // than hand back just's, which is what a search by selector name over the
  // whole datatype gives whichever constructor is named.
  EXPECT_NO_THROW(s->get_selector(maybesort, "just", "value"));
  EXPECT_THROW(s->get_selector(maybesort, "nothing", "value"),
               IncorrectUsageException);
}

TEST_P(Datatypes, ConstructorFromTermVec)
{
  DatatypeDecl tripledecl = s->make_datatype_decl("triple");
  DatatypeConstructorDecl mktriple =
      s->make_datatype_constructor_decl("mktriple");
  s->add_selector(mktriple, "first", intsort);
  s->add_selector(mktriple, "second", intsort);
  s->add_selector(mktriple, "third", intsort);
  s->add_constructor(tripledecl, mktriple);
  Sort triplesort = s->make_sort(tripledecl);

  Term three = s->make_term(3, intsort);
  Term triple =
      s->make_term(Apply_Constructor,
                   TermVec{ s->get_constructor(triplesort, "mktriple"),
                            s->make_term(1, intsort),
                            s->make_term(2, intsort),
                            three });
  Term third = s->make_term(
      Apply_Selector,
      TermVec{ s->get_selector(triplesort, "mktriple", "third"), triple });
  s->assert_formula(s->make_term(Distinct, third, three));
  EXPECT_TRUE(s->check_sat().is_unsat());
}

TEST_P(Datatypes, DeclareSimpleListWithForwardRef)
{
  if (s->get_solver_enum() == GENERIC_SOLVER)
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

TEST_P(Datatypes, DatatypeDecl)
{
  // Make datatype sort
  DatatypeDecl consListSpec = s->make_datatype_decl("list");

  auto dt_decltest = make_shared<GenericDatatypeDecl>("secondtestdt");

  std::shared_ptr<GenericDatatype> gdt =
      make_shared<GenericDatatype>(dt_decltest);
  EXPECT_EQ(gdt->get_num_constructors(), 0);

  shared_ptr<GenericDatatypeConstructorDecl> cons2test =
      shared_ptr<GenericDatatypeConstructorDecl>(
          new GenericDatatypeConstructorDecl("constest"));
  gdt->add_constructor(cons2test);
  EXPECT_EQ(gdt->get_num_constructors(), 1);
  EXPECT_EQ(gdt->get_num_selectors("constest"), 0);
  EXPECT_EQ(gdt->get_name(), "secondtestdt");

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

  EXPECT_EQ(countersort->get_sort_kind(), DATATYPE);
  EXPECT_EQ(listsort->get_sort_kind(), DATATYPE);
  EXPECT_NE(countersort, listsort);

  Datatype listdt = listsort->get_datatype();

  Term five = s->make_term(5, intsort);
  // Make datatype terms
  Term cons = s->get_constructor(listsort, "cons");
  EXPECT_EQ(cons->to_string(), "cons");
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

  EXPECT_EQ(listdt->get_name(), "list");
  EXPECT_EQ(listdt->get_num_constructors(), 2);
  EXPECT_EQ(listdt->get_num_selectors("cons"), 2);
  EXPECT_EQ(listdt->get_num_selectors("nil"), 0);

  EXPECT_TRUE(res.is_sat());
  // Expected exceptions

  EXPECT_THROW(s->get_constructor(listsort, "kons"), IncorrectUsageException);
  EXPECT_THROW(s->get_tester(listsort, "head"), IncorrectUsageException);
  EXPECT_THROW(listdt->get_num_selectors("kons"), IncorrectUsageException);
}

TEST_P(Datatypes, ComponentsAreHashConsed)
{
  DatatypeDecl maybedecl = s->make_datatype_decl("maybe");
  DatatypeConstructorDecl nothing =
      s->make_datatype_constructor_decl("nothing");
  DatatypeConstructorDecl just = s->make_datatype_constructor_decl("just");
  s->add_selector(just, "value", intsort);
  s->add_constructor(maybedecl, nothing);
  s->add_constructor(maybedecl, just);
  Sort maybesort = s->make_sort(maybedecl);

  // asking twice gives the same term, which compares their sorts
  EXPECT_EQ(s->get_constructor(maybesort, "just"),
            s->get_constructor(maybesort, "just"));
  EXPECT_EQ(s->get_selector(maybesort, "just", "value"),
            s->get_selector(maybesort, "just", "value"));
  EXPECT_EQ(s->get_tester(maybesort, "just"), s->get_tester(maybesort, "just"));
}

TEST_P(Datatypes, PrintsAsSmtlib)
{
  if (s->get_solver_enum() == GENERIC_SOLVER && !GetParam().is_logging_solver)
  {
    GTEST_SKIP() << "a generic term prints the defined name of each subterm, "
                    "and datatype ops by their smt-switch names";
  }

  DatatypeDecl listdecl = s->make_datatype_decl("list");
  DatatypeConstructorDecl nildecl = s->make_datatype_constructor_decl("nil");
  DatatypeConstructorDecl consdecl = s->make_datatype_constructor_decl("cons");
  s->add_selector(consdecl, "head", intsort);
  s->add_constructor(listdecl, nildecl);
  s->add_constructor(listdecl, consdecl);
  // after add_constructor, which the generic solver needs first (B.4)
  s->add_selector_self(consdecl, "tail");
  Sort listsort = s->make_sort(listdecl);
  EXPECT_EQ(listsort->to_string(), "list");

  // a nullary constructor applied is a constant
  Term nil =
      s->make_term(Apply_Constructor, s->get_constructor(listsort, "nil"));
  EXPECT_EQ(nil->to_string(), "nil");
  Term list5 = s->make_term(Apply_Constructor,
                            s->get_constructor(listsort, "cons"),
                            s->make_term(5, intsort),
                            nil);
  EXPECT_EQ(list5->to_string(), "(cons 5 nil)");
  EXPECT_EQ(
      s->make_term(
           Apply_Selector, s->get_selector(listsort, "cons", "head"), list5)
          ->to_string(),
      "(head (cons 5 nil))");
  EXPECT_EQ(s->make_term(Apply_Tester, s->get_tester(listsort, "nil"), nil)
                ->to_string(),
            "((_ is nil) nil)");
}

TEST_P(Datatypes, DeclName)
{
  DatatypeDecl decl = s->make_datatype_decl("list");
  EXPECT_EQ(decl->get_name(), "list");
}

INSTANTIATE_TEST_SUITE_P(
    ,
    Datatypes,
    testing::ValuesIn(filter_solver_configurations({ THEORY_DATATYPE })),
    ConfigName());

}  // namespace
