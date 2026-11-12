/*!
 * \file unit-sort.cpp
 * \brief Unit tests for sorts
 * \author Makai Mann
 * \author Áron Ricardo Perez-Lopez
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <set>
#include <sstream>
#include <string>
#include <vector>

#include "available_solvers.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"
#include "smt-switch/utils.h"

using namespace smt;
using namespace smt_tests;

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

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitSortTests);
class UnitSortTests : public testing::Test,
                      public testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");
    s->set_opt("incremental", "true");

    boolsort = s->make_sort(BOOL);
    bvsort = s->make_sort(BV, 4);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort });
    arrsort = s->make_sort(ARRAY, bvsort, bvsort);
  }
  SmtSolver s;
  Sort boolsort, bvsort, funsort, arrsort;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitSortArithTests);
class UnitSortArithTests : public UnitSortTests
{
 protected:
  void SetUp() override
  {
    UnitSortTests::SetUp();
    intsort = s->make_sort(INT);
    realsort = s->make_sort(REAL);
  }
  Sort intsort, realsort;
};

TEST_P(UnitSortTests, SameSortDiffObj)
{
  Sort boolsort_2 = s->make_sort(BOOL);
  EXPECT_EQ(boolsort->hash(), boolsort_2->hash());
  EXPECT_EQ(boolsort, boolsort_2);

  Sort bvsort_2 = s->make_sort(BV, 4);
  EXPECT_EQ(bvsort->hash(), bvsort_2->hash());
  EXPECT_EQ(bvsort, bvsort_2);

  Sort bvsort8 = s->make_sort(BV, 8);
  EXPECT_NE(bvsort, bvsort8);

  Sort funsort_2 = s->make_sort(FUNCTION, { bvsort, bvsort_2 });
  EXPECT_EQ(funsort->hash(), funsort_2->hash());
  EXPECT_EQ(funsort, funsort_2);

  Sort arrsort_2 = s->make_sort(ARRAY, bvsort, bvsort_2);
  EXPECT_EQ(arrsort->hash(), arrsort_2->hash());
  EXPECT_EQ(arrsort, arrsort_2);

  EXPECT_NE(funsort, bvsort);
}

TEST_P(UnitSortTests, OrderAgreesWithEquality)
{
  expect_order_agrees_with_equality(
      SortVec{ boolsort,
               bvsort,
               s->make_sort(BV, 4),
               s->make_sort(BV, 8),
               funsort,
               arrsort,
               s->make_sort(ARRAY, bvsort, bvsort),
               Sort() });
  std::set<Sort> ordered{ bvsort, s->make_sort(BV, 4), boolsort };
  EXPECT_EQ(ordered.size(), 2u);
}

TEST_P(UnitSortTests, SortSet)
{
  UnorderedSortSet sset{
    s->make_sort(BV, 1), s->make_sort(BV, 4), boolsort, s->make_sort(BV, 5)
  };
  // Boolector gives Bool and (_ BitVec 1) one sort, which the logging
  // solver keeps apart
  bool aliased = solver_has_attribute(GetParam().solver_enum, BOOL_BV1_ALIASING)
                 && !GetParam().is_logging_solver;
  EXPECT_EQ(sset.size(), aliased ? 3 : 4);
}

TEST(NullSort, EqualsNullSort)
{
  Sort s1, s2;
  EXPECT_EQ(s1, s2);
  EXPECT_FALSE(s1 != s2);
}

TEST(NullSort, HashesToZero) { EXPECT_EQ(std::hash<Sort>{}(Sort()), 0u); }

TEST(NullSort, PrintsNull)
{
  std::ostringstream out;
  out << Sort();
  EXPECT_EQ(out.str(), "null");
}

TEST_P(UnitSortTests, NullSortDiffersFromSort)
{
  Sort null;
  EXPECT_NE(bvsort, null);
  EXPECT_NE(null, bvsort);
  EXPECT_FALSE(bvsort == null);
  EXPECT_FALSE(null == bvsort);
}

TEST_P(UnitSortTests, NullSortInSet)
{
  UnorderedSortSet sset{ bvsort, Sort(), arrsort, Sort() };
  EXPECT_EQ(sset.size(), 3u);
  EXPECT_EQ(sset.count(Sort()), 1u);
}

TEST_P(UnitSortTests, FunctionSymbolSort)
{
  Term f = s->make_symbol("f", funsort);
  EXPECT_EQ(f->get_sort()->hash(), funsort->hash());
  EXPECT_EQ(f->get_sort(), funsort);
  SortVec domain_sorts = f->get_sort()->get_domain_sorts();
  ASSERT_EQ(domain_sorts.size(), 1);
  EXPECT_EQ(domain_sorts[0], bvsort);
  EXPECT_EQ(f->get_sort()->get_codomain_sort(), bvsort);
}

TEST_P(UnitSortTests, BinaryFunctionSymbolSort)
{
  Sort bv8 = s->make_sort(BV, 8);
  Sort binsort = s->make_sort(FUNCTION, SortVec{ bvsort, bv8, bvsort });
  Term g = s->make_symbol("g", binsort);
  EXPECT_EQ(g->get_sort(), binsort);
  SortVec domain_sorts = g->get_sort()->get_domain_sorts();
  ASSERT_EQ(domain_sorts.size(), 2);
  EXPECT_EQ(domain_sorts[0], bvsort);
  EXPECT_EQ(domain_sorts[1], bv8);
  EXPECT_EQ(g->get_sort()->get_codomain_sort(), bvsort);
}

TEST_P(UnitSortTests, ArrayTermSorts)
{
  Term a = s->make_symbol("a", arrsort);
  Term b = s->make_symbol("b", arrsort);
  Term i = s->make_symbol("i", bvsort);
  Term c = s->make_symbol("c", boolsort);
  for (const Term & t :
       TermVec{ a, s->make_term(Store, a, i, i), s->make_term(Ite, c, a, b) })
  {
    EXPECT_EQ(t->get_sort()->get_sort_kind(), ARRAY) << t;
    EXPECT_EQ(t->get_sort(), arrsort) << t;
  }
}

TEST_P(UnitSortTests, FunctionSortDomainAndCodomain)
{
  // no Bool argument: MathSAT does not take one, so its backend makes it a
  // bit-vector of width one, which the domain then reports
  Sort bvsort8 = s->make_sort(BV, 8);
  Sort binsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort8, bvsort });
  EXPECT_EQ(binsort->get_domain_sorts(), (SortVec{ bvsort, bvsort8 }));
  EXPECT_EQ(binsort->get_codomain_sort(), bvsort);
}

TEST_P(UnitSortTests, FunctionSortArrayDomain)
{
  if (s->get_solver_enum() == BTOR)
  {
    GTEST_SKIP() << "Boolector takes only Bool and bit-vector arguments";
  }
  Sort arrfunsort = s->make_sort(FUNCTION, SortVec{ arrsort, bvsort });
  Sort domain = arrfunsort->get_domain_sorts().at(0);
  EXPECT_EQ(domain, arrsort);
  EXPECT_EQ(domain->get_indexsort(), bvsort);
  EXPECT_EQ(domain->get_elemsort(), bvsort);
}

TEST_P(UnitSortTests, SortParams)
{
  EXPECT_EQ(bvsort->get_width(), 4);
  EXPECT_EQ(arrsort->get_indexsort(), bvsort);
  EXPECT_EQ(arrsort->get_elemsort(), bvsort);
  // not every solver supports querying function types for domain/codomain yet
}

TEST_P(UnitSortTests, WidthAbove32Bits)
{
  constexpr std::uint64_t width = std::uint64_t{ 1 } << 32;
  SolverEnum se = GetParam().solver_enum;
  if (se == BTOR || se == CVC5 || se == YICES2 || se == Z3)
  {
    // their APIs take 32-bit widths
    EXPECT_THROW(s->make_sort(BV, width), IncorrectUsageException);
  }
  else
  {
    EXPECT_EQ(s->make_sort(BV, width)->get_width(), width);
  }
}

TEST_P(UnitSortTests, SortKinds)
{
  // Boolector gives Bool and (_ BitVec 1) one sort, which the logging
  // solver keeps apart
  bool aliased = solver_has_attribute(GetParam().solver_enum, BOOL_BV1_ALIASING)
                 && !GetParam().is_logging_solver;
  EXPECT_EQ(boolsort->get_sort_kind(), aliased ? BV : BOOL);
  EXPECT_EQ(bvsort->get_sort_kind(), BV);
  EXPECT_EQ(funsort->get_sort_kind(), FUNCTION);
  EXPECT_EQ(arrsort->get_sort_kind(), ARRAY);
}

TEST_P(UnitSortTests, SortVecArgs)
{
  if (s->get_solver_enum() == GENERIC_SOLVER)
  {
    GTEST_SKIP() << "The generic solver takes the last sort of a FUNCTION "
                    "SortVec as the return sort without checking that any "
                    "remain, so a one-element vector gives a function of no "
                    "arguments instead of throwing";
  }
  Sort arrsort_2 = s->make_sort(ARRAY, SortVec{ bvsort, bvsort });
  EXPECT_EQ(arrsort, arrsort_2);

  EXPECT_THROW(s->make_sort(BV, SortVec{ bvsort }), IncorrectUsageException);
  EXPECT_THROW(s->make_sort(ARRAY, SortVec{ bvsort }), IncorrectUsageException);
  EXPECT_THROW(s->make_sort(ARRAY, SortVec{ bvsort, bvsort, bvsort }),
               IncorrectUsageException);
  EXPECT_THROW(s->make_sort(FUNCTION, SortVec{ bvsort }),
               IncorrectUsageException);
}

TEST_P(UnitSortTests, SortShorthands)
{
  EXPECT_EQ(s->make_sort(FUNCTION, bvsort, boolsort),
            s->make_sort(FUNCTION, SortVec{ bvsort, boolsort }));
  EXPECT_EQ(s->make_sort(FUNCTION, bvsort, bvsort, boolsort),
            s->make_sort(FUNCTION, SortVec{ bvsort, bvsort, boolsort }));
  EXPECT_EQ(
      s->make_sort(FUNCTION, bvsort, bvsort, bvsort, boolsort),
      s->make_sort(FUNCTION, SortVec{ bvsort, bvsort, bvsort, boolsort }));
  EXPECT_THROW(s->make_sort(ARRAY, bvsort), IncorrectUsageException);
}

TEST_P(UnitSortTests, AccessorsOnlyForTheirKinds)
{
  for (const Sort & sort : SortVec{ boolsort, bvsort, funsort, arrsort })
  {
    SortKind sk = sort->get_sort_kind();
    if (sk != BV)
    {
      EXPECT_THROW(sort->get_width(), IncorrectUsageException) << sort;
    }
    if (sk != ARRAY)
    {
      EXPECT_THROW(sort->get_indexsort(), IncorrectUsageException) << sort;
      EXPECT_THROW(sort->get_elemsort(), IncorrectUsageException) << sort;
    }
    if (sk != FUNCTION)
    {
      EXPECT_THROW(sort->get_domain_sorts(), IncorrectUsageException) << sort;
      EXPECT_THROW(sort->get_codomain_sort(), IncorrectUsageException) << sort;
    }
    // none of these sorts is uninterpreted or a datatype
    EXPECT_THROW(sort->get_uninterpreted_name(), IncorrectUsageException)
        << sort;
    EXPECT_THROW(sort->get_arity(), IncorrectUsageException) << sort;
    EXPECT_THROW(sort->get_uninterpreted_constructor(), IncorrectUsageException)
        << sort;
    EXPECT_THROW(sort->get_uninterpreted_param_sorts(), IncorrectUsageException)
        << sort;
    EXPECT_THROW(sort->get_datatype(), IncorrectUsageException) << sort;
  }
}

TEST_P(UnitSortArithTests, SameSortDiffObj)
{
  Sort intsort_2 = s->make_sort(INT);
  EXPECT_EQ(intsort->hash(), intsort_2->hash());
  EXPECT_EQ(intsort, intsort_2);

  Sort realsort_2 = s->make_sort(REAL);
  EXPECT_EQ(realsort->hash(), realsort_2->hash());
  EXPECT_EQ(realsort, realsort_2);
}

TEST_P(UnitSortArithTests, SortKinds)
{
  EXPECT_EQ(intsort->get_sort_kind(), INT);
  EXPECT_EQ(realsort->get_sort_kind(), REAL);
}

TEST_P(UnitSortArithTests, FunctionSortLeavesNamesFree)
{
  s->make_sort(FUNCTION, SortVec{ intsort, intsort });
  EXPECT_NO_THROW(s->make_symbol("internal_ref_fun_Int_return_Int", intsort));
}

TEST_P(UnitSortArithTests, FunctionSortAfterSymbolOfAnyName)
{
  s->make_symbol("internal_ref_fun_Int_return_Int", intsort);
  Sort f = s->make_sort(FUNCTION, SortVec{ intsort, intsort });
  EXPECT_EQ(f->get_domain_sorts(), SortVec{ intsort });
  EXPECT_EQ(f->get_codomain_sort(), intsort);
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UninterpretedSorts);
class UninterpretedSorts : public UnitSortTests
{
 protected:
  void SetUp() override
  {
    UnitSortTests::SetUp();
    usort = s->make_sort("U", 0);
    a = s->make_symbol("a", usort);
    b = s->make_symbol("b", usort);
    f = s->make_symbol("f", s->make_sort(FUNCTION, SortVec{ usort, bvsort }));
    one = s->make_term(1, bvsort);
    two = s->make_term(2, bvsort);
  }

  Term apply_f(const Term & t) const { return s->make_term(Apply, f, t); }

  Sort usort;
  Term a, b, f, one, two;
};

TEST_P(UninterpretedSorts, NullarySort)
{
  EXPECT_EQ(usort->get_sort_kind(), UNINTERPRETED);
  EXPECT_EQ(usort->get_uninterpreted_name(), "U");
  EXPECT_EQ(usort->get_arity(), 0);
  EXPECT_THROW(usort->get_uninterpreted_constructor(), IncorrectUsageException);
  EXPECT_TRUE(usort->get_uninterpreted_param_sorts().empty());
}

TEST_P(UninterpretedSorts, EqualTermsHaveEqualValues)
{
  if (s->get_solver_enum() == GENERIC_SOLVER)
  {
    GTEST_SKIP() << "The generic solver cannot get the value of a term whose "
                    "sort kind is Uninterpreted";
  }
  EXPECT_EQ(a->get_sort(), usort);
  EXPECT_EQ(a->get_sort(), b->get_sort());

  s->push();
  s->assert_formula(s->make_term(Equal, a, b));
  ASSERT_TRUE(s->check_sat().is_sat());
  Term a_value = s->get_value(a);
  Term b_value = s->get_value(b);
  s->pop();

  EXPECT_EQ(a_value, b_value);
  EXPECT_TRUE(a_value->is_value());
  EXPECT_FALSE(a_value->is_symbol());

  s->assert_formula(s->make_term(Distinct, a, b));
  s->assert_formula(s->make_term(Equal, a, a_value));
  s->assert_formula(s->make_term(Equal, b, b_value));
  EXPECT_TRUE(s->check_sat().is_unsat());
}

TEST_P(UninterpretedSorts, FunctionTellsTermsApart)
{
  s->assert_formula(s->make_term(Equal, apply_f(a), one));
  s->assert_formula(s->make_term(Equal, apply_f(b), two));
  EXPECT_TRUE(s->check_sat().is_sat());
}

TEST_P(UninterpretedSorts, FunctionIsCongruentThroughIte)
{
  Term c = s->make_symbol("c", boolsort);
  s->assert_formula(c);
  s->assert_formula(
      s->make_term(Equal, apply_f(s->make_term(Ite, c, a, b)), one));
  s->assert_formula(s->make_term(Equal, apply_f(a), two));
  EXPECT_TRUE(s->check_sat().is_unsat());
}

TEST_P(UninterpretedSorts, ArrayIndexedBySortReadsItsStore)
{
  Term arr = s->make_symbol("arr", s->make_sort(ARRAY, usort, bvsort));
  Term stored = s->make_term(Store, arr, a, one);
  s->assert_formula(s->make_term(Equal, s->make_term(Select, stored, a), two));
  EXPECT_TRUE(s->check_sat().is_unsat());
}

TEST_P(UninterpretedSorts, AssertedEqualityIsUsed)
{
  s->assert_formula(s->make_term(Equal, a, b));
  s->assert_formula(s->make_term(Equal, apply_f(a), one));
  s->assert_formula(s->make_term(Equal, apply_f(b), two));
  EXPECT_TRUE(s->check_sat().is_unsat());
}

TEST_P(UninterpretedSorts, NameAsMadePrintedInBars)
{
  if (s->get_solver_enum() == GENERIC_SOLVER)
  {
    GTEST_SKIP() << "the generic solver declares a sort's name to the binary "
                    "without SMT-LIB quoting";
  }
  Sort sort = s->make_sort("my sort", 0);
  EXPECT_EQ(sort->get_uninterpreted_name(), "my sort");
  EXPECT_EQ(sort->to_string(), "|my sort|");
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(SortConstructors);
class SortConstructors : public UnitSortTests
{
 protected:
  void SetUp() override
  {
    UnitSortTests::SetUp();
    elem = s->make_sort("E", 0);
    list = s->make_sort("List", 1);
  }

  Sort elem, list;
};

// the sort of a term is the applied sort, with its name and parameters
TEST_P(SortConstructors, ConstructorOfArityFour)
{
  Sort sort_cons = s->make_sort("sort-con", 4);
  EXPECT_EQ(sort_cons->get_sort_kind(), UNINTERPRETED_CONS);
  EXPECT_EQ(sort_cons->get_arity(), 4);
  EXPECT_THROW(sort_cons->get_uninterpreted_constructor(),
               IncorrectUsageException);

  EXPECT_THROW(s->make_sort(sort_cons, SortVec{ bvsort, bvsort, bvsort }),
               IncorrectUsageException);
  // only a sort constructor can be applied
  EXPECT_THROW(s->make_sort(elem, SortVec{ bvsort }), IncorrectUsageException);
  EXPECT_THROW(s->make_sort(bvsort, SortVec{ bvsort }),
               IncorrectUsageException);

  Sort param_sort =
      s->make_sort(sort_cons, SortVec{ bvsort, bvsort, bvsort, bvsort });
  EXPECT_EQ(param_sort->get_sort_kind(), UNINTERPRETED);
  // an applied sort is named after its constructor
  EXPECT_EQ(param_sort->get_uninterpreted_name(), "sort-con");
  EXPECT_EQ(param_sort->get_uninterpreted_constructor(), sort_cons);
  EXPECT_EQ(param_sort->get_uninterpreted_param_sorts(),
            (SortVec{ bvsort, bvsort, bvsort, bvsort }));

  // but is identified and printed by its parameters too
  EXPECT_EQ(param_sort,
            s->make_sort(sort_cons, SortVec{ bvsort, bvsort, bvsort, bvsort }));
  EXPECT_NE(param_sort,
            s->make_sort(sort_cons,
                         SortVec{ boolsort, boolsort, boolsort, boolsort }));
  EXPECT_EQ(param_sort->to_string(),
            "(sort-con (_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4))");
  EXPECT_EQ(sort_cons->to_string(), "sort-con");
}

TEST_P(SortConstructors, SortOfATerm)
{
  Sort list_e = s->make_sort(list, SortVec{ elem });
  Sort sort = s->make_symbol("x", list_e)->get_sort();
  EXPECT_EQ(sort, list_e);
  EXPECT_EQ(sort->get_sort_kind(), UNINTERPRETED);
  EXPECT_EQ(sort->get_uninterpreted_name(), "List");
  EXPECT_EQ(sort->get_uninterpreted_constructor(), list);
  EXPECT_EQ(sort->get_uninterpreted_param_sorts(), SortVec{ elem });
  EXPECT_EQ(sort->to_string(), "(List E)");
}

TEST_P(SortConstructors, FunctionOverAppliedSortIsCongruent)
{
  Sort list_e = s->make_sort(list, SortVec{ elem });
  Term x = s->make_symbol("x", list_e);
  Term y = s->make_symbol("y", list_e);
  Term c = s->make_symbol("c", boolsort);
  Term f =
      s->make_symbol("f", s->make_sort(FUNCTION, SortVec{ list_e, bvsort }));
  s->assert_formula(c);
  s->assert_formula(
      s->make_term(Equal,
                   s->make_term(Apply, f, s->make_term(Ite, c, x, y)),
                   s->make_term(1, bvsort)));
  s->assert_formula(
      s->make_term(Equal, s->make_term(Apply, f, x), s->make_term(2, bvsort)));
  EXPECT_TRUE(s->check_sat().is_unsat());
}

TEST_P(SortConstructors, ConstructorIsNotATermSort)
{
  if (s->get_solver_enum() == GENERIC_SOLVER)
  {
    GTEST_SKIP() << "the generic solver accepts a sort constructor as the "
                    "sort of a param, in an array or function sort, and as a "
                    "sort constructor's argument";
  }
  EXPECT_THROW(s->make_symbol("x", list), IncorrectUsageException);
  EXPECT_THROW(s->make_param("p", list), IncorrectUsageException);
  EXPECT_THROW(s->make_sort(ARRAY, list, bvsort), IncorrectUsageException);
  EXPECT_THROW(s->make_sort(ARRAY, bvsort, list), IncorrectUsageException);
  EXPECT_THROW(s->make_sort(FUNCTION, SortVec{ list, bvsort }),
               IncorrectUsageException);
  EXPECT_THROW(s->make_sort(FUNCTION, SortVec{ bvsort, list }),
               IncorrectUsageException);
  EXPECT_THROW(s->make_sort(list, SortVec{ list }), IncorrectUsageException);
}

TEST_P(SortConstructors, SameNamedConstructorsDiffer)
{
  if (s->get_solver_enum() == GENERIC_SOLVER)
  {
    GTEST_SKIP() << "the generic solver refuses to declare a second sort with "
                    "the same name";
  }
  Sort other = s->make_sort("List", 1);
  if (other == list)
  {
    GTEST_SKIP() << "this solver returns the existing sort constructor when "
                    "one with the same name is declared again";
  }
  EXPECT_NE(s->make_sort(other, SortVec{ elem }),
            s->make_sort(list, SortVec{ elem }));
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(QuantifiedSortConstructors);
class QuantifiedSortConstructors : public SortConstructors
{
};

TEST_P(QuantifiedSortConstructors, BinderPrintsAppliedSort)
{
  if (!GetParam().is_logging_solver && GetParam().solver_enum == GENERIC_SOLVER)
  {
    GTEST_SKIP() << "the generic solver prints a quantifier without its "
                    "binders' sorts";
  }
  Sort list_e = s->make_sort(list, SortVec{ elem });
  Term p = s->make_param("p", list_e);
  Term f =
      s->make_symbol("f", s->make_sort(FUNCTION, SortVec{ list_e, boolsort }));
  Term forall = s->make_term(Forall, p, s->make_term(Apply, f, p));
  EXPECT_THAT(
      forall->to_string(),
      testing::AllOf(
          testing::HasSubstr("(List E)"),
          testing::Not(testing::HasSubstr(std::string(INTERNAL_NAME_PREFIX)))));
}

TEST_P(QuantifiedSortConstructors, BarredSymbolPrintsAsNamed)
{
  if (!GetParam().is_logging_solver && GetParam().solver_enum == GENERIC_SOLVER)
  {
    GTEST_SKIP() << "the generic solver prints a quantifier without its "
                    "binders' sorts";
  }
  Sort list_e = s->make_sort(list, SortVec{ elem });
  std::string name = "x " + internal_name("sort", 0);
  Term x = s->make_symbol(name, list_e);
  Term p = s->make_param("p", list_e);
  Term forall = s->make_term(Forall, p, s->make_term(Equal, p, x));
  EXPECT_THAT(forall->to_string(),
              testing::AllOf(testing::HasSubstr("(List E)"),
                             testing::HasSubstr("|" + name + "|")));
}

INSTANTIATE_TEST_SUITE_P(ParameterizedUnitSortTests,
                         UnitSortTests,
                         testing::ValuesIn(available_solver_configurations()));

INSTANTIATE_TEST_SUITE_P(ParameterizedUnitSortArithTests,
                         UnitSortArithTests,
                         testing::ValuesIn(filter_solver_configurations(
                             { THEORY_INT, THEORY_REAL })));

INSTANTIATE_TEST_SUITE_P(
    UnitSort,
    UninterpretedSorts,
    testing::ValuesIn(filter_solver_configurations({ UNINTERP_SORT })),
    ConfigName());

INSTANTIATE_TEST_SUITE_P(
    UnitSort,
    SortConstructors,
    testing::ValuesIn(filter_solver_configurations({ PARAM_UNINTERP_SORT })),
    ConfigName());

INSTANTIATE_TEST_SUITE_P(UnitSort,
                         QuantifiedSortConstructors,
                         testing::ValuesIn(filter_solver_configurations(
                             { PARAM_UNINTERP_SORT, QUANTIFIERS })),
                         ConfigName());

}  // namespace
