/*!
 * \file test-logging-solver.cpp
 * \brief Tests for LoggingSolver infrastructure
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <memory>
#include <string>
#include <vector>

#include "available_solvers.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/logging_solver.h"
#include "smt-switch/ops.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(Logging);
class Logging : public ::testing::Test,
                public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    // IMPORTANT : make sure not to use doubly nested LoggingSolvers
    // can mess things up
    // Thus, need to use the "lite" version of solvers
    // before wrapping with a LoggingSolver
    s = make_shared<LoggingSolver>(create_solver(GetParam()));
    s->set_opt("produce-models", "true");
    bvsort4 = s->make_sort(BV, 4);
    bvsort8 = s->make_sort(BV, 8);
    arraysort = s->make_sort(ARRAY, bvsort4, bvsort8);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort4, bvsort8 });

    x = s->make_symbol("x", bvsort4);
    y = s->make_symbol("y", bvsort4);
    zero = s->make_term(0, bvsort4);
    one = s->make_term(1, bvsort4);
  }
  SmtSolver s;
  Sort bvsort4, bvsort8, arraysort, funsort;
  Term x, y, zero, one;
};

TEST_P(Logging, Children)
{
  EXPECT_TRUE(x->get_op().is_null());
  EXPECT_TRUE(y->is_symbolic_const());
  EXPECT_FALSE(y->is_value());

  Term xp1 = s->make_term(BVAdd, x, one);
  EXPECT_EQ(xp1->get_op(), BVAdd);
  TermVec children;
  for (auto tt : xp1)
  {
    children.push_back(tt);
  }
  EXPECT_EQ(children[0], x);
  EXPECT_EQ(children[1], one);
}

TEST_P(Logging, PrintsApplicationAsSmtlib)
{
  Term f = s->make_symbol("f", funsort);
  EXPECT_EQ(s->make_term(Apply, f, x)->to_string(), "(f x)");
}

TEST_P(Logging, PrintsQuotedSymbolName)
{
  Term spaced = s->make_symbol("my x", bvsort4);
  EXPECT_EQ(spaced->to_string(), "|my x|");
  EXPECT_EQ(s->get_symbol("my x"), spaced);
}

TEST_P(Logging, PrintsIndexedOpAsSmtlib)
{
  EXPECT_EQ(s->make_term(Op(Rotate_Right, 2), x)->to_string(),
            "((_ rotate_right 2) x)");
  EXPECT_EQ(s->make_term(Op(Rotate_Left, 2), x)->to_string(),
            "((_ rotate_left 2) x)");
}

TEST_P(Logging, HashConsing)
{
  Term xp1 = s->make_term(BVAdd, x, one);
  // Check hash-consing using comparison of underlying pointers
  Term xp1_2 = s->make_term(BVAdd, x, one);
  EXPECT_EQ(xp1.get(), xp1_2.get());
}

TEST_P(Logging, Sorts)
{
  Term cond = s->make_term(BVUge, x, zero);
  EXPECT_EQ(cond->get_sort()->get_sort_kind(), BOOL);
  Term relu = s->make_term(Ite, cond, x, zero);
  EXPECT_EQ(relu->get_sort(), x->get_sort());
}

TEST_P(Logging, ConstantSorts)
{
  Term t = s->make_term(true);
  Term f = s->make_term(false);
  EXPECT_NE(t, f);
  EXPECT_EQ(t, t);

  Sort bvsort1 = s->make_sort(BV, 1);
  Term bv0 = s->make_term(0, bvsort1);
  Term bv1 = s->make_term(1, bvsort1);
  EXPECT_NE(bv0, bv1);
  EXPECT_EQ(bv1, bv1);

  EXPECT_NE(f, bv0);
  EXPECT_NE(f, bv1);
  EXPECT_NE(t, bv0);
  EXPECT_NE(t, bv1);

  EXPECT_EQ(t->get_sort()->get_sort_kind(), BOOL);
  EXPECT_EQ(bv0->get_sort()->get_sort_kind(), BV);
  EXPECT_EQ(bv1->get_sort()->get_width(), 1);
}

TEST_P(Logging, Compare)
{
  Term f = s->make_symbol("f", funsort);
  Term fx = s->make_term(Apply, f, x);
  Term fx2 = s->make_term(Apply, f, x);
  EXPECT_EQ(fx, fx2);

  Term fy = s->make_term(Apply, f, y);
  EXPECT_NE(fx, fy);

  Term x_eq_y = s->make_term(Equal, x, y);
  Term x_eq_y2 = s->make_term(Equal, x, y);
  EXPECT_EQ(x_eq_y, x_eq_y2);

  // LoggingTerms do no rewriting or normalization
  // you always get exactly what you created
  Term y_eq_x = s->make_term(Equal, y, x);
  EXPECT_NE(x_eq_y, y_eq_x);

  s->assert_formula(x_eq_y);

  Result r = s->check_sat();
  ASSERT_TRUE(r.is_sat());

  // compare values
  // they should be hash-consed correctly in LoggingSolver
  // so that comparison works as expected
  Term xv = s->get_value(x);
  Term yv = s->get_value(y);
  EXPECT_EQ(xv, yv);

  Term fxv = s->get_value(fx);
  Term fxv2 = s->get_value(fx2);
  Term fyv = s->get_value(fy);
  EXPECT_EQ(fxv, fxv2);
  EXPECT_EQ(fxv, fyv);
}

TEST_P(Logging, WrongKindAccessors)
{
  Sort boolsort = s->make_sort(BOOL);
  EXPECT_THROW(boolsort->get_width(), IncorrectUsageException);
  EXPECT_THROW(boolsort->get_indexsort(), IncorrectUsageException);
  EXPECT_THROW(boolsort->get_elemsort(), IncorrectUsageException);
  EXPECT_THROW(boolsort->get_domain_sorts(), IncorrectUsageException);
  EXPECT_THROW(boolsort->get_codomain_sort(), IncorrectUsageException);
  EXPECT_THROW(boolsort->get_uninterpreted_name(), IncorrectUsageException);
  EXPECT_THROW(boolsort->get_arity(), IncorrectUsageException);
  EXPECT_THROW(boolsort->get_uninterpreted_param_sorts(),
               IncorrectUsageException);
  EXPECT_THROW(boolsort->get_datatype(), IncorrectUsageException);
  // a subclass inherits the accessors its kind lacks
  EXPECT_THROW(bvsort4->get_elemsort(), IncorrectUsageException);
}

TEST_P(Logging, TermFromAnotherSolver)
{
  if (GetParam().solver_enum == GENERIC_SOLVER)
  {
    GTEST_SKIP() << "generic terms compare by their text, so another generic "
                    "solver's x is taken for this one's";
  }
  SmtSolver s2 = make_shared<LoggingSolver>(create_solver(GetParam()));
  Term x2 = s2->make_symbol("x", s2->make_sort(BV, 4));
  EXPECT_THROW(s->make_term(BVAdd, x, x2), IncorrectUsageException);
}

TEST_P(Logging, NullTerm)
{
  EXPECT_THROW(s->make_term(BVAdd, x, Term()), IncorrectUsageException);
  EXPECT_THROW(s->make_term(Term(), arraysort), IncorrectUsageException);
  EXPECT_THROW(s->get_value(Term()), IncorrectUsageException);
  Term out_const_base;
  EXPECT_THROW(s->get_array_values(Term(), out_const_base),
               IncorrectUsageException);
  EXPECT_THROW(s->assert_formula(Term()), IncorrectUsageException);
  EXPECT_THROW(s->check_sat_assuming(TermVec{ Term() }),
               IncorrectUsageException);
}

TEST_P(Logging, NullSort)
{
  EXPECT_THROW(s->make_sort(ARRAY, SortVec{ bvsort4, Sort() }),
               IncorrectUsageException);
  EXPECT_THROW(s->make_sort(Sort(), SortVec{ bvsort4 }),
               IncorrectUsageException);
  EXPECT_THROW(s->make_term(0, Sort()), IncorrectUsageException);
  EXPECT_THROW(s->make_term(std::string("a"), true, Sort()),
               IncorrectUsageException);
  EXPECT_THROW(s->make_term(std::wstring(L"a"), Sort()),
               IncorrectUsageException);
  EXPECT_THROW(s->make_term(std::string("1"), Sort()), IncorrectUsageException);
  EXPECT_THROW(s->make_term(zero, Sort()), IncorrectUsageException);
  EXPECT_THROW(s->make_symbol("z", Sort()), IncorrectUsageException);
  EXPECT_THROW(s->make_param("p", Sort()), IncorrectUsageException);
  EXPECT_THROW(s->get_constructor(Sort(), "c"), IncorrectUsageException);
  EXPECT_THROW(s->get_tester(Sort(), "c"), IncorrectUsageException);
  EXPECT_THROW(s->get_selector(Sort(), "c", "f"), IncorrectUsageException);
}

TEST_P(Logging, NullDatatypeDeclaration)
{
  DatatypeDecl decl;
  DatatypeConstructorDecl con;
  EXPECT_THROW(s->make_sort(decl), IncorrectUsageException);
  EXPECT_THROW(s->make_datatype_sorts({ decl }), IncorrectUsageException);
  EXPECT_THROW(s->add_constructor(decl, con), IncorrectUsageException);
  EXPECT_THROW(s->add_selector(con, "f", bvsort4), IncorrectUsageException);
  EXPECT_THROW(s->add_selector_self(con, "f"), IncorrectUsageException);
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(LoggingUninterpretedArrays);
class LoggingUninterpretedArrays : public Logging
{
};

TEST_P(LoggingUninterpretedArrays, ValuesHoldAssertedEntry)
{
  SolverEnum se = GetParam().solver_enum;
  if (se == MSAT)
  {
    GTEST_SKIP() << "MathSAT's model of an array indexed by an uninterpreted "
                    "sort is a constant array without the asserted entry";
  }
  if (se == GENERIC_SOLVER)
  {
    GTEST_SKIP() << "the generic solver cannot read back a value of an "
                    "uninterpreted sort";
  }
  Sort usort = s->make_sort("U", 0);
  Term arr = s->make_symbol("arr", s->make_sort(ARRAY, usort, bvsort8));
  Term u = s->make_symbol("u", usort);
  Term one8 = s->make_term(1, bvsort8);
  s->assert_formula(s->make_term(Equal, s->make_term(Select, arr, u), one8));
  ASSERT_TRUE(s->check_sat().is_sat());

  Term base;
  UnorderedTermMap values = s->get_array_values(arr, base);
  // the entry at u's value, or else the constant base, is the asserted one
  auto it = values.find(s->get_value(u));
  EXPECT_EQ(it != values.end() ? it->second : base, one8);
}

INSTANTIATE_TEST_SUITE_P(
    ,
    Logging,
    testing::ValuesIn(available_solver_configurations_with_generic()),
    ConfigName());

INSTANTIATE_TEST_SUITE_P(
    ,
    LoggingUninterpretedArrays,
    testing::ValuesIn(filter_solver_configurations_with_generic(
        { UNINTERP_SORT, ARRAY_MODELS })),
    ConfigName());

}  // namespace
