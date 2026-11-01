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

#include <gtest/gtest.h>

#include <cstddef>
#include <functional>
#include <map>
#include <memory>
#include <set>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

#include "available_solvers.h"
#include "datatype.h"
#include "exceptions.h"
#include "generic_datatype.h"
#include "ops.h"
#include "result.h"
#include "smt_defs.h"
#include "solver.h"
#include "solver_enums.h"
#include "sort.h"
#include "term.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

// For every pair, neither is less than the other exactly when they are
// equal.
template <typename T>
void expect_order_agrees_with_equality(const std::vector<T> & xs)
{
  for (std::size_t i = 0; i < xs.size(); i++)
  {
    for (std::size_t j = 0; j < xs.size(); j++)
    {
      const T & a = xs[i];
      const T & b = xs[j];
      EXPECT_EQ(!(a < b) && !(b < a), a == b) << i << " and " << j;
      EXPECT_FALSE(a < b && b < a) << i << " and " << j;
      EXPECT_EQ(a <= b, !(b < a)) << i << " and " << j;
      EXPECT_EQ(a > b, b < a) << i << " and " << j;
    }
  }
}

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
  s->add_selector_self(consdecl, "tail");
  s->add_constructor(consListSpec, nildecl);
  s->add_constructor(consListSpec, consdecl);
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
  EXPECT_EQ(listdt->get_constructor_names(), (vector<string>{ "nil", "cons" }));
  EXPECT_EQ(listdt->get_selector_names("cons"),
            (vector<string>{ "head", "tail" }));
  EXPECT_TRUE(listdt->get_selector_names("nil").empty());
  EXPECT_EQ(listdt->get_selector_sort("cons", "head"), intsort);
  EXPECT_EQ(listdt->get_selector_sort("cons", "tail"), listsort);

  EXPECT_TRUE(res.is_sat());
  // Expected exceptions

  EXPECT_THROW(s->get_constructor(listsort, "kons"), IncorrectUsageException);
  EXPECT_THROW(s->get_tester(listsort, "head"), IncorrectUsageException);
  EXPECT_THROW(listdt->get_num_selectors("kons"), IncorrectUsageException);
  EXPECT_THROW(listdt->get_selector_names("kons"), IncorrectUsageException);
  EXPECT_THROW(listdt->get_selector_sort("kons", "head"),
               IncorrectUsageException);
  EXPECT_THROW(listdt->get_selector_sort("nil", "head"),
               IncorrectUsageException);
  // a constructor's sort is not its datatype's
  EXPECT_THROW(cons->get_sort()->get_datatype(), IncorrectUsageException);
  EXPECT_THROW(s->get_constructor(cons->get_sort(), "nil"),
               IncorrectUsageException);
}

TEST_P(Datatypes, NamesReachEveryComponent)
{
  Sort boolsort = s->make_sort(BOOL);
  DatatypeDecl treedecl = s->make_datatype_decl("tree");
  DatatypeConstructorDecl leafdecl = s->make_datatype_constructor_decl("leaf");
  DatatypeConstructorDecl nodedecl = s->make_datatype_constructor_decl("node");
  s->add_selector(nodedecl, "flag", boolsort);
  s->add_selector(nodedecl, "value", intsort);
  s->add_selector_self(nodedecl, "child");
  s->add_constructor(treedecl, leafdecl);
  s->add_constructor(treedecl, nodedecl);
  Sort treesort = s->make_sort(treedecl);

  map<string, Sort> declared{ { "flag", boolsort },
                              { "value", intsort },
                              { "child", treesort } };
  Datatype dt = treesort->get_datatype();
  EXPECT_EQ(dt->get_constructor_names(), (vector<string>{ "leaf", "node" }));
  EXPECT_EQ(dt->get_selector_names("node"),
            (vector<string>{ "flag", "value", "child" }));
  for (const string & con : dt->get_constructor_names())
  {
    EXPECT_NO_THROW(s->get_tester(treesort, con)) << con;
    SortVec domain =
        s->get_constructor(treesort, con)->get_sort()->get_domain_sorts();
    vector<string> selectors = dt->get_selector_names(con);
    ASSERT_EQ(domain.size(), selectors.size()) << con;
    for (size_t i = 0; i < selectors.size(); ++i)
    {
      Sort selsort = s->get_selector(treesort, con, selectors[i])
                         ->get_sort()
                         ->get_codomain_sort();
      EXPECT_EQ(selsort, declared.at(selectors[i])) << selectors[i];
      EXPECT_EQ(dt->get_selector_sort(con, selectors[i]), selsort)
          << selectors[i];
      EXPECT_EQ(domain[i], selsort) << selectors[i];
    }
  }
}

TEST_P(Datatypes, ConstructorDeclChangedAfterMakeSort)
{
  DatatypeConstructorDecl cons = s->make_datatype_constructor_decl("cons");
  s->add_selector(cons, "head", intsort);
  DatatypeDecl adecl = s->make_datatype_decl("a");
  s->add_constructor(adecl, cons);
  Sort asort = s->make_sort(adecl);

  // the sort keeps the constructor as it was when its declaration was used
  s->add_selector_self(cons, "tail");
  DatatypeDecl bdecl = s->make_datatype_decl("b");
  DatatypeConstructorDecl nil = s->make_datatype_constructor_decl("nil");
  s->add_constructor(bdecl, nil);
  s->add_constructor(bdecl, cons);
  Sort bsort = s->make_sort(bdecl);

  Datatype adt = asort->get_datatype();
  EXPECT_EQ(adt->get_selector_names("cons"), (vector<string>{ "head" }));
  EXPECT_EQ(
      s->get_constructor(asort, "cons")->get_sort()->get_domain_sorts().size(),
      1u);
  EXPECT_THROW(s->get_selector(asort, "cons", "tail"), IncorrectUsageException);

  Datatype bdt = bsort->get_datatype();
  EXPECT_EQ(bdt->get_selector_names("cons"),
            (vector<string>{ "head", "tail" }));
  EXPECT_EQ(bdt->get_selector_sort("cons", "tail"), bsort);
  EXPECT_EQ(
      s->get_constructor(bsort, "cons")->get_sort()->get_domain_sorts().size(),
      2u);
}

TEST_P(Datatypes, SecondMakeSortRefused)
{
  DatatypeDecl unitdecl = s->make_datatype_decl("unit");
  DatatypeConstructorDecl u = s->make_datatype_constructor_decl("u");
  s->add_constructor(unitdecl, u);
  s->make_sort(unitdecl);
  EXPECT_THROW(s->make_sort(unitdecl), IncorrectUsageException);
}

TEST_P(Datatypes, MakeDatatypeSortsMakesEach)
{
  if (s->get_solver_enum() == GENERIC_SOLVER)
  {
    GTEST_SKIP() << "the generic solver refuses every make_datatype_sorts";
  }
  std::vector<DatatypeDecl> decls;
  for (const string & name : vector<string>{ "a", "b", "c" })
  {
    DatatypeDecl decl = s->make_datatype_decl(name);
    DatatypeConstructorDecl con =
        s->make_datatype_constructor_decl("mk" + name);
    s->add_selector(con, "get" + name, intsort);
    s->add_constructor(decl, con);
    decls.push_back(decl);
  }
  SortVec sorts = s->make_datatype_sorts(decls);
  ASSERT_EQ(sorts.size(), 3u);
  for (size_t i = 0; i < sorts.size(); ++i)
  {
    string name = decls[i]->get_name();
    Datatype dt = sorts[i]->get_datatype();
    EXPECT_EQ(dt->get_name(), name);
    EXPECT_EQ(dt->get_constructor_names(), (vector<string>{ "mk" + name }));
    EXPECT_EQ(dt->get_selector_sort("mk" + name, "get" + name), intsort);
  }
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
  s->add_selector_self(consdecl, "tail");
  s->add_constructor(listdecl, nildecl);
  s->add_constructor(listdecl, consdecl);
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

TEST_P(Datatypes, ConstructorDeclName)
{
  DatatypeConstructorDecl cons = s->make_datatype_constructor_decl("cons");
  EXPECT_EQ(cons->get_name(), "cons");
}

TEST_P(Datatypes, DatatypeComparesByDatatype)
{
  DatatypeDecl maybedecl = s->make_datatype_decl("maybe");
  DatatypeConstructorDecl nothing =
      s->make_datatype_constructor_decl("nothing");
  DatatypeConstructorDecl just = s->make_datatype_constructor_decl("just");
  s->add_selector(just, "value", intsort);
  s->add_constructor(maybedecl, nothing);
  s->add_constructor(maybedecl, just);
  Sort maybesort = s->make_sort(maybedecl);

  DatatypeDecl unitdecl = s->make_datatype_decl("unit");
  s->add_constructor(unitdecl, s->make_datatype_constructor_decl("tt"));
  Sort unitsort = s->make_sort(unitdecl);

  // a backend may hand back a new Datatype on every call
  Datatype maybe = maybesort->get_datatype();
  Datatype maybe_again = maybesort->get_datatype();
  EXPECT_EQ(maybe, maybe_again);
  EXPECT_EQ(std::hash<Datatype>{}(maybe), std::hash<Datatype>{}(maybe_again));
  std::unordered_set<Datatype> unique{ maybe, maybe_again };
  EXPECT_EQ(unique.size(), 1u);
  EXPECT_NE(maybe, unitsort->get_datatype());
}

TEST_P(Datatypes, EqualConstructorDeclsHashAlike)
{
  DatatypeConstructorDecl just = s->make_datatype_constructor_decl("just");
  s->add_selector(just, "value", intsort);
  DatatypeConstructorDecl just_again =
      s->make_datatype_constructor_decl("just");
  s->add_selector(just_again, "value", intsort);
  ASSERT_EQ(just, just_again);
  EXPECT_EQ(std::hash<DatatypeConstructorDecl>{}(just),
            std::hash<DatatypeConstructorDecl>{}(just_again));
  std::unordered_set<DatatypeConstructorDecl> unique{ just, just_again };
  EXPECT_EQ(unique.size(), 1u);
}

TEST_P(Datatypes, ConstructorDeclsCompareSelectorSorts)
{
  if (s->get_solver_enum() == GENERIC_SOLVER)
  {
    GTEST_SKIP() << "a generic constructor declaration compares by its name "
                    "only";
  }
  DatatypeConstructorDecl just_int = s->make_datatype_constructor_decl("just");
  s->add_selector(just_int, "value", intsort);
  DatatypeConstructorDecl just_bool = s->make_datatype_constructor_decl("just");
  s->add_selector(just_bool, "value", s->make_sort(BOOL));
  EXPECT_NE(just_int, just_bool);
}

TEST_P(Datatypes, ConstructorDeclEqualityOutlivesItsDatatype)
{
  DatatypeConstructorDecl just = s->make_datatype_constructor_decl("just");
  s->add_selector(just, "value", intsort);
  DatatypeDecl maybedecl = s->make_datatype_decl("maybe");
  s->add_constructor(maybedecl, just);
  s->make_sort(maybedecl);

  DatatypeConstructorDecl just_again =
      s->make_datatype_constructor_decl("just");
  s->add_selector(just_again, "value", intsort);
  ASSERT_EQ(just, just_again);
  EXPECT_EQ(std::hash<DatatypeConstructorDecl>{}(just),
            std::hash<DatatypeConstructorDecl>{}(just_again));
}

TEST_P(Datatypes, SelfSelectorsCompareAlikeAcrossDatatypes)
{
  DatatypeConstructorDecl cons = s->make_datatype_constructor_decl("cons");
  s->add_selector(cons, "head", intsort);
  s->add_selector_self(cons, "tail");
  DatatypeDecl listdecl = s->make_datatype_decl("list");
  s->add_constructor(listdecl, s->make_datatype_constructor_decl("nil"));
  s->add_constructor(listdecl, cons);

  DatatypeConstructorDecl cons_again =
      s->make_datatype_constructor_decl("cons");
  s->add_selector(cons_again, "head", intsort);
  s->add_selector_self(cons_again, "tail");
  DatatypeDecl stackdecl = s->make_datatype_decl("stack");
  s->add_constructor(stackdecl, s->make_datatype_constructor_decl("nil"));
  s->add_constructor(stackdecl, cons_again);

  ASSERT_EQ(cons, cons_again);
  std::size_t hash_before = std::hash<DatatypeConstructorDecl>{}(cons);
  EXPECT_EQ(std::hash<DatatypeConstructorDecl>{}(cons_again), hash_before);
  EXPECT_FALSE(cons < cons_again);

  s->make_sort(listdecl);
  EXPECT_EQ(cons, cons_again);
  EXPECT_EQ(std::hash<DatatypeConstructorDecl>{}(cons), hash_before);
  EXPECT_EQ(std::hash<DatatypeConstructorDecl>{}(cons_again), hash_before);
}

TEST_P(Datatypes, OrderAgreesWithEquality)
{
  DatatypeConstructorDecl nothing =
      s->make_datatype_constructor_decl("nothing");
  DatatypeConstructorDecl just = s->make_datatype_constructor_decl("just");
  s->add_selector(just, "value", intsort);
  DatatypeConstructorDecl just_again =
      s->make_datatype_constructor_decl("just");
  s->add_selector(just_again, "value", intsort);

  DatatypeDecl maybedecl = s->make_datatype_decl("maybe");
  s->add_constructor(maybedecl, s->make_datatype_constructor_decl("none"));
  Sort maybesort = s->make_sort(maybedecl);

  DatatypeDecl unitdecl = s->make_datatype_decl("unit");
  s->add_constructor(unitdecl, s->make_datatype_constructor_decl("tt"));
  Sort unitsort = s->make_sort(unitdecl);

  expect_order_agrees_with_equality(std::vector<DatatypeConstructorDecl>{
      nothing, just, just_again, DatatypeConstructorDecl() });
  std::set<DatatypeConstructorDecl> ordered{ just, just_again };
  EXPECT_EQ(ordered.size(), 1u);

  std::vector<Datatype> datatypes{ maybesort->get_datatype(),
                                   maybesort->get_datatype(),
                                   unitsort->get_datatype(),
                                   Datatype() };
  expect_order_agrees_with_equality(datatypes);
  EXPECT_EQ(std::set<Datatype>(datatypes.begin(), datatypes.end()).size(), 3u);
}

INSTANTIATE_TEST_SUITE_P(
    ,
    Datatypes,
    testing::ValuesIn(filter_solver_configurations({ THEORY_DATATYPE })),
    ConfigName());

}  // namespace
