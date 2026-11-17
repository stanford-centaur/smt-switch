/*!
 * \file unit-sort-inference.cpp
 * \brief Unit tests for sort inference
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <cstdint>
#include <limits>
#include <memory>
#include <string>
#include <unordered_set>
#include <vector>

#include "available_solvers.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

namespace smt::tests {

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitSortInferenceTests);
class UnitSortInferenceTests
    : public testing::Test,
      public testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");

    boolsort = s->make_sort(BOOL);
    bvsort4 = s->make_sort(BV, 4);
    bvsort5 = s->make_sort(BV, 5);
    arrsort = s->make_sort(ARRAY, bvsort4, bvsort4);
    funsort = s->make_sort(FUNCTION, { bvsort4, bvsort4, boolsort });

    b1 = s->make_symbol("b1", boolsort);
    b2 = s->make_symbol("b2", boolsort);
    p = s->make_symbol("p", bvsort4);
    q = s->make_symbol("q", bvsort4);
    w = s->make_symbol("w", bvsort5);
    arr = s->make_symbol("arr", arrsort);
    f = s->make_symbol("f", funsort);
  }
  SmtSolver s;
  Sort boolsort, bvsort4, bvsort5, arrsort, funsort;
  Term b1, b2, p, q, w, arr, f;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitArithmeticSortInferenceTests);
class UnitArithmeticSortInferenceTests : public UnitSortInferenceTests
{
 protected:
  void SetUp() override
  {
    UnitSortInferenceTests::SetUp();
    realsort = s->make_sort(REAL);
    intsort = s->make_sort(INT);

    x = s->make_symbol("x", realsort);
    y = s->make_symbol("y", realsort);
    z = s->make_symbol("z", realsort);

    xint = s->make_symbol("xint", intsort);
    yint = s->make_symbol("yint", intsort);
    zint = s->make_symbol("zint", intsort);
  }
  Sort realsort, intsort;
  Term x, y, z, xint, yint, zint;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(DatatypeSortedness);
class DatatypeSortedness : public UnitSortInferenceTests
{
};

TEST_P(UnitSortInferenceTests, SortRules)
{
  EXPECT_TRUE(Op(Equal).check_sortedness(SortVec{ boolsort, boolsort }));
  EXPECT_TRUE(Op(Equal).check_sortedness(SortVec{ bvsort4, bvsort4 }));
  EXPECT_TRUE(Op(Equal).check_sortedness(SortVec{ arrsort, arrsort }));
  EXPECT_TRUE(Op(Equal).check_sortedness(SortVec{ funsort, funsort }));
  EXPECT_FALSE(Op(Equal).check_sortedness(SortVec{ boolsort, bvsort4 }));
  EXPECT_FALSE(Op(Equal).check_sortedness(SortVec{ bvsort4, bvsort5 }));

  EXPECT_FALSE(Op(Ite).check_sortedness(SortVec{ boolsort, bvsort4, bvsort5 }));

  EXPECT_TRUE(Op(Ite).check_sortedness(SortVec{ boolsort, bvsort4, bvsort4 }));
  EXPECT_TRUE(Op(Not).check_sortedness(SortVec{ boolsort }));

  EXPECT_TRUE(Op(BVNot).check_sortedness(SortVec{ bvsort4 }));
}

TEST_P(UnitSortInferenceTests, SortednessTooFewSorts)
{
  EXPECT_FALSE(Op(Equal).check_sortedness(SortVec{}));
  EXPECT_FALSE(Op(Ite).check_sortedness(SortVec{}));
  EXPECT_FALSE(Op(Ite).check_sortedness(SortVec{ boolsort, bvsort4 }));
  EXPECT_FALSE(Op(Apply).check_sortedness(SortVec{}));
  EXPECT_FALSE(Op(BVAnd).check_sortedness(SortVec{}));
  EXPECT_FALSE(Op(Select).check_sortedness(SortVec{}));
  EXPECT_FALSE(Op(Store).check_sortedness(SortVec{}));
}

TEST_P(UnitSortInferenceTests, SortComputationTooFewArguments)
{
  EXPECT_THROW(Op(And).compute_sort(s, SortVec{}), IncorrectUsageException);
  EXPECT_THROW(Op(Concat).compute_sort(s, SortVec{ bvsort4 }),
               IncorrectUsageException);
  EXPECT_THROW(Op(Concat).compute_sort(s, TermVec{ p }),
               IncorrectUsageException);
  EXPECT_THROW(Op(Ite).compute_sort(s, TermVec{ b1, p }),
               IncorrectUsageException);
}

TEST_P(UnitSortInferenceTests, SortednessTests)
{
  /******** Booleans ********/
  EXPECT_TRUE(Op(Equal).check_sortedness({ b1, b2 }));
  EXPECT_TRUE(Op(Distinct).check_sortedness({ b1, b2 }));

  EXPECT_TRUE(Op(And).check_sortedness({ b1, b2 }));
  EXPECT_TRUE(Op(Xor).check_sortedness({ b1, b2 }));
  // wrong operator, except where Booleans are bit-vectors of width one
  if (!solver_has_attribute(s->get_solver_enum(),
                            SolverAttribute::BOOL_BV1_ALIASING))
  {
    EXPECT_FALSE(Op(BVAnd).check_sortedness({ b1, b2 }));
  }

  EXPECT_FALSE(Op(Ge).check_sortedness({ b1, b2 }));

  // wrong number of arguments
  EXPECT_FALSE(Op(Xor).check_sortedness({ b1 }));

  /******* Bitvectors *******/
  EXPECT_TRUE(Op(Equal).check_sortedness({ p, q }));
  EXPECT_TRUE(Op(Distinct).check_sortedness({ p, q }));
  EXPECT_TRUE(Op(BVAdd).check_sortedness({ p, q }));
  EXPECT_TRUE(Op(BVAnd).check_sortedness({ p, q }));
  EXPECT_TRUE(Op(BVAdd).check_sortedness({ p, q }));
  EXPECT_TRUE(Op(BVUlt).check_sortedness({ p, q }));
  EXPECT_TRUE(Op(BVNeg).check_sortedness({ p }));
  // different bit-widths
  EXPECT_FALSE(Op(BVAdd).check_sortedness({ p, w }));
  EXPECT_FALSE(Op(Distinct).check_sortedness({ p, w }));

  /********* Arrays ********/
  EXPECT_TRUE(Op(Select).check_sortedness({ arr, p }));
  EXPECT_TRUE(Op(Store).check_sortedness({ arr, p, q }));
  EXPECT_TRUE(
      Op(Equal).check_sortedness({ arr, s->make_term(Store, arr, p, q) }));
  // wrong bit-width
  EXPECT_FALSE(Op(Select).check_sortedness({ arr, w }));
  EXPECT_FALSE(Op(Store).check_sortedness({ arr, p, w }));
  EXPECT_FALSE(Op(Store).check_sortedness({ arr, w, p }));

  // BTOR doesn't support getting the sort of a function yet
  if (s->get_solver_enum() != BTOR)
  {
    /********* Functions ********/
    EXPECT_TRUE(Op(Apply).check_sortedness({ f, p, q }));
    // wrong type
    EXPECT_FALSE(Op(Apply).check_sortedness({ f, p, w }));
    EXPECT_FALSE(Op(Apply).check_sortedness({ f, arr, q }));
    // wrong number of arguments
    EXPECT_FALSE(Op(Apply).check_sortedness({ f }));
    EXPECT_FALSE(Op(Apply).check_sortedness({ f, p }));
    EXPECT_FALSE(Op(Apply).check_sortedness({ f, arr }));
  }

  /************** Quantifiers (if supported) ******************/
  if (solver_has_attribute(s->get_solver_enum(), SolverAttribute::QUANTIFIERS))
  {
    Term param = s->make_param("param", bvsort4);
    EXPECT_TRUE(param->is_param());
    Term body = s->make_term(Equal, param, s->make_term(0, bvsort4));
    EXPECT_TRUE(Op(Exists).check_sortedness({ param, body }));
    // not a parameter
    EXPECT_FALSE(Op(Exists).check_sortedness({ q, body }));
    // not a formula for the body
    EXPECT_FALSE(
        Op(Exists).check_sortedness({ param, s->make_term(BVAdd, param, q) }));

    // bind param
    Term forallparam = s->make_term(Forall, param, body);
    EXPECT_TRUE(param->is_param());  // should still be considered a parameter
                                     // after binding
  }
}

TEST_P(UnitSortInferenceTests, SortComputationBVIndexBounds)
{
  EXPECT_EQ(Op(Extract, 3, 3).compute_sort(s, { bvsort4 })->get_width(), 1);
  EXPECT_THROW(Op(Extract, 2, 3).compute_sort(s, { bvsort4 }),
               IncorrectUsageException);
  EXPECT_THROW(Op(Extract, 4, 0).compute_sort(s, { bvsort4 }),
               IncorrectUsageException);
}

TEST_P(UnitSortInferenceTests, SortComputationWidthOverflow)
{
  constexpr std::uint64_t max = std::numeric_limits<std::uint64_t>::max();
  EXPECT_THROW(Op(Zero_Extend, max).compute_sort(s, { bvsort4 }),
               IncorrectUsageException);
  EXPECT_THROW(Op(Sign_Extend, max - 3).compute_sort(s, { bvsort4 }),
               IncorrectUsageException);
  EXPECT_THROW(Op(Repeat, max / 4 + 1).compute_sort(s, { bvsort4 }),
               IncorrectUsageException);
  if (GetParam().solver_enum == GENERIC_SOLVER)
  {
    // its sorts are smt-switch's own, so they can be this wide
    Sort wide = s->make_sort(BV, max - 3);
    EXPECT_THROW(Op(Concat).compute_sort(s, { wide, bvsort4 }),
                 IncorrectUsageException);
  }
}

TEST_P(UnitSortInferenceTests, SortComputation)
{
  /******** Booleans ********/
  EXPECT_EQ(boolsort, Op(Equal).compute_sort(s, { b1, b2 }));
  EXPECT_EQ(boolsort, Op(Equal).compute_sort(s, { boolsort, boolsort }));
  EXPECT_EQ(boolsort, Op(Distinct).compute_sort(s, { boolsort, boolsort }));

  /******* Bitvectors *******/
  EXPECT_EQ(boolsort, Op(Equal).compute_sort(s, { p, q }));
  EXPECT_EQ(boolsort, Op(Equal).compute_sort(s, { bvsort4, bvsort4 }));
  EXPECT_EQ(boolsort, Op(BVUlt).compute_sort(s, { p, q }));
  EXPECT_EQ(boolsort, Op(BVUlt).compute_sort(s, { bvsort4, bvsort4 }));
  EXPECT_EQ(bvsort4, Op(BVAdd).compute_sort(s, { p, q }));
  EXPECT_EQ(bvsort4, Op(BVAdd).compute_sort(s, { bvsort4, bvsort4 }));
  EXPECT_EQ(bvsort4, Op(BVNeg).compute_sort(s, { p }));
  EXPECT_EQ(bvsort4, Op(BVNeg).compute_sort(s, { bvsort4 }));

  Sort bvsort3 = s->make_sort(BV, 3);
  Sort bvsort9 = s->make_sort(BV, 9);
  Sort bvsort12 = s->make_sort(BV, 12);
  EXPECT_EQ(bvsort3, Op(Extract, 2, 0).compute_sort(s, { p }));
  EXPECT_EQ(bvsort3, Op(Extract, 2, 0).compute_sort(s, { bvsort4 }));
  EXPECT_EQ(bvsort9, Op(Concat).compute_sort(s, { p, w }));
  EXPECT_EQ(bvsort12, Op(Repeat, 3).compute_sort(s, { p }));

  EXPECT_NE(bvsort9, Op(Concat).compute_sort(s, { bvsort4, bvsort4 }));

  // /********* Arrays ********/
  EXPECT_EQ(bvsort4, Op(Select).compute_sort(s, { arr, p }));
  EXPECT_EQ(bvsort4, Op(Select).compute_sort(s, { arrsort, bvsort4 }));
  EXPECT_EQ(arrsort, Op(Store).compute_sort(s, { arrsort, bvsort4, bvsort4 }));
  EXPECT_EQ(arrsort, Op(Store).compute_sort(s, { arr, p, q }));

  // BTOR doesn't support getting the sort of a function yet
  if (s->get_solver_enum() != BTOR)
  {
    /********* Functions ********/
    EXPECT_EQ(boolsort, Op(Apply).compute_sort(s, { f, p, q }));
    EXPECT_EQ(boolsort,
              Op(Apply).compute_sort(s, { funsort, bvsort4, bvsort4 }));
  }
}

TEST_P(UnitArithmeticSortInferenceTests, ArithmeticSortedness)
{
  EXPECT_TRUE(Op(Gt).check_sortedness({ x, y }));
  EXPECT_TRUE(Op(Ge).check_sortedness({ xint, yint }));
  EXPECT_TRUE(Op(Lt).check_sortedness({ x, y }));
  EXPECT_TRUE(Op(Le).check_sortedness({ xint, yint }));

  EXPECT_TRUE(Op(Plus).check_sortedness({ x, y }));
  EXPECT_TRUE(Op(Plus).check_sortedness({ xint, yint }));
  EXPECT_TRUE(Op(Minus).check_sortedness({ x, y }));
  EXPECT_TRUE(Op(Minus).check_sortedness({ xint, yint }));
  EXPECT_TRUE(Op(Negate).check_sortedness({ xint }));
  EXPECT_TRUE(Op(Abs).check_sortedness({ xint }));

  EXPECT_TRUE(Op(To_Int).check_sortedness({ x }));
  EXPECT_TRUE(Op(To_Real).check_sortedness({ xint }));
  EXPECT_TRUE(Op(Is_Int).check_sortedness({ x }));

  // wrong operators
  EXPECT_FALSE(Op(To_Real).check_sortedness({ x }));
  EXPECT_FALSE(Op(To_Int).check_sortedness({ xint }));
  EXPECT_FALSE(Op(Is_Int).check_sortedness({ xint }));
  EXPECT_FALSE(Op(BVUgt).check_sortedness({ x, y }));
  EXPECT_FALSE(Op(BVSgt).check_sortedness({ xint, yint }));
  EXPECT_FALSE(Op(BVUlt).check_sortedness({ x, y }));
  EXPECT_FALSE(Op(BVSge).check_sortedness({ xint, yint }));
  EXPECT_FALSE(Op(BVAdd).check_sortedness({ xint, yint }));

  // wrong number of arguments
  EXPECT_FALSE(Op(Negate).check_sortedness({ xint, yint }));
  EXPECT_FALSE(Op(Abs).check_sortedness({ xint, yint }));
}

TEST_P(UnitArithmeticSortInferenceTests, ArithmeticSortComputation)
{
  EXPECT_EQ(boolsort, Op(Equal).compute_sort(s, { x, y }));
  EXPECT_EQ(boolsort, Op(Equal).compute_sort(s, { realsort, realsort }));

  EXPECT_EQ(boolsort, Op(Ge).compute_sort(s, { x, y }));
  EXPECT_EQ(boolsort, Op(Le).compute_sort(s, { realsort, realsort }));

  EXPECT_EQ(realsort, Op(Plus).compute_sort(s, { x, y }));
  EXPECT_EQ(realsort, Op(Minus).compute_sort(s, { realsort, realsort }));

  EXPECT_EQ(intsort, Op(Plus).compute_sort(s, { xint, yint }));
  EXPECT_EQ(intsort, Op(Minus).compute_sort(s, { intsort, intsort }));

  // over an Int and a Real, the result is a Real
  EXPECT_EQ(realsort, Op(Plus).compute_sort(s, { xint, y }));
  EXPECT_EQ(realsort, Op(Minus).compute_sort(s, { x, yint }));
  EXPECT_EQ(realsort, Op(Mult).compute_sort(s, { intsort, realsort, intsort }));

  Sort aritharrsort = s->make_sort(ARRAY, intsort, realsort);
  Term aritharr = s->make_symbol("aritharr", aritharrsort);

  // /********* Arrays ********/
  EXPECT_EQ(realsort, Op(Select).compute_sort(s, { aritharr, yint }));
  EXPECT_EQ(realsort, Op(Select).compute_sort(s, { aritharrsort, intsort }));
  EXPECT_EQ(aritharrsort,
            Op(Store).compute_sort(s, { aritharrsort, intsort, realsort }));
  EXPECT_EQ(aritharrsort, Op(Store).compute_sort(s, { aritharr, xint, y }));
}

TEST_P(DatatypeSortedness, ComponentApplications)
{
  DatatypeDecl maybedecl = s->make_datatype_decl("maybe");
  DatatypeConstructorDecl nothingdecl =
      s->make_datatype_constructor_decl("nothing");
  DatatypeConstructorDecl justdecl = s->make_datatype_constructor_decl("just");
  s->add_selector(justdecl, "value", bvsort4);
  s->add_constructor(maybedecl, nothingdecl);
  s->add_constructor(maybedecl, justdecl);
  Sort maybesort = s->make_sort(maybedecl);

  Term nothing = s->get_constructor(maybesort, "nothing");
  Term just = s->get_constructor(maybesort, "just");
  Term is_just = s->get_tester(maybesort, "just");
  Term value = s->get_selector(maybesort, "just", "value");
  Term m = s->make_symbol("m", maybesort);

  EXPECT_TRUE(Op(Apply_Constructor).check_sortedness({ nothing }));
  EXPECT_TRUE(Op(Apply_Constructor).check_sortedness({ just, p }));
  EXPECT_TRUE(Op(Apply_Tester).check_sortedness({ is_just, m }));
  EXPECT_TRUE(Op(Apply_Selector).check_sortedness({ value, m }));

  // a head that is not a datatype component
  EXPECT_FALSE(Op(Apply_Constructor).check_sortedness({ p }));
  EXPECT_FALSE(Op(Apply_Tester).check_sortedness({ p, m }));
  EXPECT_FALSE(Op(Apply_Selector).check_sortedness({ arr, m }));
  // an argument that is not a datatype term
  EXPECT_FALSE(Op(Apply_Tester).check_sortedness({ is_just, p }));
  EXPECT_FALSE(Op(Apply_Selector).check_sortedness({ value, p }));
  // a missing argument
  EXPECT_FALSE(Op(Apply_Tester).check_sortedness({ is_just }));
  EXPECT_FALSE(Op(Apply_Selector).check_sortedness({ value }));
}

TEST_P(DatatypeSortedness, ComponentApplicationSorts)
{
  DatatypeDecl maybedecl = s->make_datatype_decl("maybe");
  DatatypeConstructorDecl nothingdecl =
      s->make_datatype_constructor_decl("nothing");
  DatatypeConstructorDecl justdecl = s->make_datatype_constructor_decl("just");
  s->add_selector(justdecl, "value", bvsort4);
  s->add_constructor(maybedecl, nothingdecl);
  s->add_constructor(maybedecl, justdecl);
  Sort maybesort = s->make_sort(maybedecl);
  Term m = s->make_symbol("m", maybesort);

  EXPECT_EQ(Op(Apply_Constructor)
                .compute_sort(s, { s->get_constructor(maybesort, "just"), p }),
            maybesort);
  EXPECT_EQ(
      Op(Apply_Tester).compute_sort(s, { s->get_tester(maybesort, "just"), m }),
      s->make_sort(BOOL));
  EXPECT_EQ(
      Op(Apply_Selector)
          .compute_sort(s, { s->get_selector(maybesort, "just", "value"), m }),
      bvsort4);
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedUnitSortInference,
    UnitSortInferenceTests,
    testing::ValuesIn(available_solver_configurations_with_generic()));

INSTANTIATE_TEST_SUITE_P(
    ParameterizedUnitArithmeticSortInference,
    UnitArithmeticSortInferenceTests,
    testing::ValuesIn(filter_solver_configurations_with_generic(
        { SolverAttribute::THEORY_INT, SolverAttribute::THEORY_REAL })));

INSTANTIATE_TEST_SUITE_P(
    UnitSortInference,
    DatatypeSortedness,
    testing::ValuesIn(filter_solver_configurations_with_generic(
        { SolverAttribute::THEORY_DATATYPE })),
    ConfigName());

}  // namespace

}  // namespace smt::tests
