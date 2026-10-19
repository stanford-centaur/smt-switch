/*********************                                                        */
/*! \file unit-sort-inference.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Unit tests for sort inference
**
**
**/

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"
#include "sort_inference.h"

using namespace smt;
using namespace std;

namespace smt_tests {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitSortInferenceTests);
class UnitSortInferenceTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
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

TEST_P(UnitSortInferenceTests, HelperTests)
{
  EXPECT_TRUE(equal_sorts({ boolsort, boolsort }));
  EXPECT_TRUE(equal_sorts({ bvsort4, bvsort4 }));
  EXPECT_TRUE(equal_sorts({ arrsort, arrsort }));
  EXPECT_TRUE(equal_sorts({ funsort, funsort }));
  EXPECT_FALSE(equal_sorts({ boolsort, bvsort4 }));
  EXPECT_FALSE(equal_sorts({ bvsort4, bvsort5 }));

  EXPECT_TRUE(equal_sortkinds({ bvsort4, bvsort5 }));
  EXPECT_TRUE(equal_sortkinds({ funsort, funsort }));
  EXPECT_FALSE(equal_sortkinds({ funsort, bvsort4 }));

  EXPECT_FALSE(check_ite_sorts({ boolsort, bvsort4, bvsort5 }));

  // if solver aliases booleans and bitvectors of width 1, this test fails
  if (!solver_has_attribute(s->get_solver_enum(), BOOL_BV1_ALIASING))
  {
    EXPECT_TRUE(check_ite_sorts({ boolsort, bvsort4, bvsort4 }));
    EXPECT_TRUE(bool_sorts({ boolsort }));
  }

  EXPECT_TRUE(bv_sorts({ bvsort4 }));
  EXPECT_TRUE(array_sorts({ arrsort }));
  EXPECT_TRUE(function_sorts({ funsort }));
}

TEST_P(UnitSortInferenceTests, SortednessTests)
{
  /******** Booleans ********/
  EXPECT_TRUE(check_sortedness(Equal, { b1, b2 }));
  EXPECT_TRUE(check_sortedness(Distinct, { b1, b2 }));

  // wrong operator
  // if solver aliases booleans and bitvectors of width 1, this test fails
  if (!solver_has_attribute(s->get_solver_enum(), BOOL_BV1_ALIASING))
  {
    EXPECT_TRUE(check_sortedness(And, { b1, b2 }));
    EXPECT_TRUE(check_sortedness(Xor, { b1, b2 }));
    EXPECT_FALSE(check_sortedness(BVAnd, { b1, b2 }));
  }

  EXPECT_FALSE(check_sortedness(Ge, { b1, b2 }));

  // wrong number of arguments
  EXPECT_FALSE(check_sortedness(Xor, { b1 }));

  /******* Bitvectors *******/
  EXPECT_TRUE(check_sortedness(Equal, { p, q }));
  EXPECT_TRUE(check_sortedness(Distinct, { p, q }));
  EXPECT_TRUE(check_sortedness(BVAdd, { p, q }));
  EXPECT_TRUE(check_sortedness(BVAnd, { p, q }));
  EXPECT_TRUE(check_sortedness(BVAdd, { p, q }));
  EXPECT_TRUE(check_sortedness(BVUlt, { p, q }));
  EXPECT_TRUE(check_sortedness(BVNeg, { p }));
  // different bit-widths
  EXPECT_FALSE(check_sortedness(BVAdd, { p, w }));
  EXPECT_FALSE(check_sortedness(Distinct, { p, w }));

  /********* Arrays ********/
  EXPECT_TRUE(check_sortedness(Select, { arr, p }));
  EXPECT_TRUE(check_sortedness(Store, { arr, p, q }));
  EXPECT_TRUE(check_sortedness(Equal, { arr, s->make_term(Store, arr, p, q) }));
  // wrong bit-width
  EXPECT_FALSE(check_sortedness(Select, { arr, w }));
  EXPECT_FALSE(check_sortedness(Store, { arr, p, w }));
  EXPECT_FALSE(check_sortedness(Store, { arr, w, p }));

  // BTOR doesn't support getting the sort of a function yet
  if (s->get_solver_enum() != BTOR)
  {
    /********* Functions ********/
    EXPECT_TRUE(check_sortedness(Apply, { f, p, q }));
    // wrong type
    EXPECT_FALSE(check_sortedness(Apply, { f, p, w }));
    EXPECT_FALSE(check_sortedness(Apply, { f, arr, q }));
    // wrong number of arguments
    EXPECT_FALSE(check_sortedness(Apply, { f }));
    EXPECT_FALSE(check_sortedness(Apply, { f, p }));
    EXPECT_FALSE(check_sortedness(Apply, { f, arr }));
  }

  /************** Quantifiers (if supported) ******************/
  if (solver_has_attribute(s->get_solver_enum(), QUANTIFIERS))
  {
    Term param = s->make_param("param", bvsort4);
    EXPECT_TRUE(param->is_param());
    Term body = s->make_term(Equal, param, s->make_term(0, bvsort4));
    // if bool and bv1 aliased, then body won't necessarily have type bool
    // e.g. BTOR also returns the type as BV1
    if (!solver_has_attribute(s->get_solver_enum(), BOOL_BV1_ALIASING))
    {
      EXPECT_TRUE(check_sortedness(Exists, { param, body }));
    }
    // not a parameter
    EXPECT_FALSE(check_sortedness(Exists, { q, body }));
    // not a formula for the body
    EXPECT_FALSE(
        check_sortedness(Exists, { param, s->make_term(BVAdd, param, q) }));

    // bind param
    Term forallparam = s->make_term(Forall, param, body);
    EXPECT_TRUE(param->is_param());  // should still be considered a parameter
                                     // after binding
  }
}

TEST_P(UnitSortInferenceTests, SortComputation)
{
  /******** Booleans ********/
  EXPECT_EQ(boolsort, compute_sort(Equal, s, { b1, b2 }));
  EXPECT_EQ(boolsort, compute_sort(Equal, s, { boolsort, boolsort }));
  EXPECT_EQ(boolsort, compute_sort(Distinct, s, { boolsort, boolsort }));

  /******* Bitvectors *******/
  EXPECT_EQ(boolsort, compute_sort(Equal, s, { p, q }));
  EXPECT_EQ(boolsort, compute_sort(Equal, s, { bvsort4, bvsort4 }));
  EXPECT_EQ(boolsort, compute_sort(BVUlt, s, { p, q }));
  EXPECT_EQ(boolsort, compute_sort(BVUlt, s, { bvsort4, bvsort4 }));
  EXPECT_EQ(bvsort4, compute_sort(BVAdd, s, { p, q }));
  EXPECT_EQ(bvsort4, compute_sort(BVAdd, s, { bvsort4, bvsort4 }));
  EXPECT_EQ(bvsort4, compute_sort(BVNeg, s, { p }));
  EXPECT_EQ(bvsort4, compute_sort(BVNeg, s, { bvsort4 }));

  Sort bvsort3 = s->make_sort(BV, 3);
  Sort bvsort9 = s->make_sort(BV, 9);
  Sort bvsort12 = s->make_sort(BV, 12);
  EXPECT_EQ(bvsort3, compute_sort(Op(Extract, 2, 0), s, { p }));
  EXPECT_EQ(bvsort3, compute_sort(Op(Extract, 2, 0), s, { bvsort4 }));
  EXPECT_EQ(bvsort9, compute_sort(Concat, s, { p, w }));
  EXPECT_EQ(bvsort12, compute_sort(Op(Repeat, 3), s, { p }));

  EXPECT_NE(bvsort9, compute_sort(Concat, s, { bvsort4, bvsort4 }));

  // /********* Arrays ********/
  EXPECT_EQ(bvsort4, compute_sort(Select, s, { arr, p }));
  EXPECT_EQ(bvsort4, compute_sort(Select, s, { arrsort, bvsort4 }));
  EXPECT_EQ(arrsort, compute_sort(Store, s, { arrsort, bvsort4, bvsort4 }));
  EXPECT_EQ(arrsort, compute_sort(Store, s, { arr, p, q }));

  // BTOR doesn't support getting the sort of a function yet
  if (s->get_solver_enum() != BTOR)
  {
    /********* Functions ********/
    EXPECT_EQ(boolsort, compute_sort(Apply, s, { f, p, q }));
    EXPECT_EQ(boolsort, compute_sort(Apply, s, { funsort, bvsort4, bvsort4 }));
  }
}

TEST_P(UnitArithmeticSortInferenceTests, ArithmeticSortedness)
{
  EXPECT_TRUE(check_sortedness(Gt, { x, y }));
  EXPECT_TRUE(check_sortedness(Ge, { xint, yint }));
  EXPECT_TRUE(check_sortedness(Lt, { x, y }));
  EXPECT_TRUE(check_sortedness(Le, { xint, yint }));

  EXPECT_TRUE(check_sortedness(Plus, { x, y }));
  EXPECT_TRUE(check_sortedness(Plus, { xint, yint }));
  EXPECT_TRUE(check_sortedness(Minus, { x, y }));
  EXPECT_TRUE(check_sortedness(Minus, { xint, yint }));
  EXPECT_TRUE(check_sortedness(Negate, { xint }));
  EXPECT_TRUE(check_sortedness(Abs, { xint }));

  EXPECT_TRUE(check_sortedness(To_Int, { x }));
  EXPECT_TRUE(check_sortedness(To_Real, { xint }));
  EXPECT_TRUE(check_sortedness(Is_Int, { x }));

  // wrong operators
  EXPECT_FALSE(check_sortedness(To_Real, { x }));
  EXPECT_FALSE(check_sortedness(To_Int, { xint }));
  EXPECT_FALSE(check_sortedness(Is_Int, { xint }));
  EXPECT_FALSE(check_sortedness(BVUgt, { x, y }));
  EXPECT_FALSE(check_sortedness(BVSgt, { xint, yint }));
  EXPECT_FALSE(check_sortedness(BVUlt, { x, y }));
  EXPECT_FALSE(check_sortedness(BVSge, { xint, yint }));
  EXPECT_FALSE(check_sortedness(BVAdd, { xint, yint }));

  // wrong number of arguments
  EXPECT_FALSE(check_sortedness(Negate, { xint, yint }));
  EXPECT_FALSE(check_sortedness(Abs, { xint, yint }));
}

TEST_P(UnitArithmeticSortInferenceTests, ArithmeticSortComputation)
{
  EXPECT_EQ(boolsort, compute_sort(Equal, s, { x, y }));
  EXPECT_EQ(boolsort, compute_sort(Equal, s, { realsort, realsort }));

  EXPECT_EQ(boolsort, compute_sort(Ge, s, { x, y }));
  EXPECT_EQ(boolsort, compute_sort(Le, s, { realsort, realsort }));

  EXPECT_EQ(realsort, compute_sort(Plus, s, { x, y }));
  EXPECT_EQ(realsort, compute_sort(Minus, s, { realsort, realsort }));

  EXPECT_EQ(intsort, compute_sort(Plus, s, { xint, yint }));
  EXPECT_EQ(intsort, compute_sort(Minus, s, { intsort, intsort }));

  Sort aritharrsort = s->make_sort(ARRAY, intsort, realsort);
  Term aritharr = s->make_symbol("aritharr", aritharrsort);

  // /********* Arrays ********/
  EXPECT_EQ(realsort, compute_sort(Select, s, { aritharr, yint }));
  EXPECT_EQ(realsort, compute_sort(Select, s, { aritharrsort, intsort }));
  EXPECT_EQ(aritharrsort,
            compute_sort(Store, s, { aritharrsort, intsort, realsort }));
  EXPECT_EQ(aritharrsort, compute_sort(Store, s, { aritharr, xint, y }));
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

  EXPECT_TRUE(check_sortedness(Apply_Constructor, { nothing }));
  EXPECT_TRUE(check_sortedness(Apply_Constructor, { just, p }));
  EXPECT_TRUE(check_sortedness(Apply_Tester, { is_just, m }));
  EXPECT_TRUE(check_sortedness(Apply_Selector, { value, m }));

  // a head that is no datatype component
  EXPECT_FALSE(check_sortedness(Apply_Constructor, { p }));
  EXPECT_FALSE(check_sortedness(Apply_Tester, { p, m }));
  EXPECT_FALSE(check_sortedness(Apply_Selector, { arr, m }));
  // an argument that is no datatype term
  EXPECT_FALSE(check_sortedness(Apply_Tester, { is_just, p }));
  EXPECT_FALSE(check_sortedness(Apply_Selector, { value, p }));
  // a missing argument
  EXPECT_FALSE(check_sortedness(Apply_Tester, { is_just }));
  EXPECT_FALSE(check_sortedness(Apply_Selector, { value }));
}

TEST_P(DatatypeSortedness, ComponentApplicationSorts)
{
  if (GetParam().solver_enum == CVC5 && !GetParam().is_logging_solver)
  {
    GTEST_SKIP() << "cvc5 gives a constructor or selector sort no codomain";
  }

  DatatypeDecl maybedecl = s->make_datatype_decl("maybe");
  DatatypeConstructorDecl nothingdecl =
      s->make_datatype_constructor_decl("nothing");
  DatatypeConstructorDecl justdecl = s->make_datatype_constructor_decl("just");
  s->add_selector(justdecl, "value", bvsort4);
  s->add_constructor(maybedecl, nothingdecl);
  s->add_constructor(maybedecl, justdecl);
  Sort maybesort = s->make_sort(maybedecl);
  Term m = s->make_symbol("m", maybesort);

  EXPECT_EQ(
      compute_sort(
          Apply_Constructor, s, { s->get_constructor(maybesort, "just"), p }),
      maybesort);
  EXPECT_EQ(
      compute_sort(Apply_Tester, s, { s->get_tester(maybesort, "just"), m }),
      s->make_sort(BOOL));
  EXPECT_EQ(compute_sort(Apply_Selector,
                         s,
                         { s->get_selector(maybesort, "just", "value"), m }),
            bvsort4);
}

INSTANTIATE_TEST_SUITE_P(ParameterizedUnitSortInference,
                         UnitSortInferenceTests,
                         testing::ValuesIn(available_solver_configurations()));

INSTANTIATE_TEST_SUITE_P(ParameterizedUnitArithmeticSortInference,
                         UnitArithmeticSortInferenceTests,
                         testing::ValuesIn(filter_solver_configurations(
                             { THEORY_INT, THEORY_REAL })));

INSTANTIATE_TEST_SUITE_P(
    UnitSortInference,
    DatatypeSortedness,
    testing::ValuesIn(filter_solver_configurations({ THEORY_DATATYPE })),
    ConfigName());

}  // namespace smt_tests
