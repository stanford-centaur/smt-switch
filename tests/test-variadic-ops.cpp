/*!
 * \file test-variadic-ops.cpp
 * \brief Tests for applying n-ary operators
 * \author Makai Mann
 * \author Po-Chun Chien
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <cstddef>
#include <exception>
#include <memory>
#include <string>
#include <unordered_set>
#include <vector>

#include "available_solvers.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/solver_utils.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(VariadicOpsTests);
class VariadicOpsTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override { s = create_solver(GetParam()); }
  SmtSolver s;
};

TEST_P(VariadicOpsTests, NoArguments)
{
  for (PrimOp po : { And, Implies, Equal, Distinct, BVAdd, Forall, Exists })
  {
    EXPECT_THROW(s->make_term(po, TermVec{}), IncorrectUsageException)
        << to_string(po);
  }
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverVariadicOpsTests,
    VariadicOpsTests,
    testing::ValuesIn(available_non_generic_solver_configurations()));

/** Checks a backend's applications of an operator to more than two arguments
 *  against make_nary_term, which builds them from applications to two as
 *  SMT-LIB defines them. Where the solver applies the operator to more
 *  arguments itself, as cvc5 and Bitwuzla do and Z3 and Yices2 do for some
 *  operators, this checks make_nary_term against the solver. Elsewhere the
 *  backend uses make_nary_term, and this checks that it takes the
 *  applications.
 */
class NaryTests : public ::testing::Test,
                  public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("incremental", "true");
  }

  /** Expects the applications of op to three and to four arguments of sort,
   *  and to three through the overload taking three, to be equal to
   *  make_nary_term's in every model
   */
  void check(PrimOp op)
  {
    SCOPED_TRACE(to_string(op));
    try
    {
      TermVec args = make_args(sort, 4);
      expect_equivalent(s->make_term(op, args),
                        make_nary_term(s.get(), op, args));
      args.pop_back();
      expect_equivalent(s->make_term(op, args),
                        make_nary_term(s.get(), op, args));
      expect_equivalent(s->make_term(op, args[0], args[1], args[2]),
                        make_nary_term(s.get(), op, args));
    }
    catch (std::exception & e)
    {
      ADD_FAILURE() << e.what();
    }
  }

  /** Makes n new symbols of the given sort */
  TermVec make_args(const Sort & arg_sort, std::size_t n)
  {
    TermVec args;
    for (std::size_t i = 0; i < n; ++i)
    {
      args.push_back(
          s->make_symbol("x" + std::to_string(next_symbol++), arg_sort));
    }
    return args;
  }

  /** Expects term and expected to be equal in every model */
  void expect_equivalent(const Term & term, const Term & expected)
  {
    s->push();
    s->assert_formula(s->make_term(Not, s->make_term(Equal, term, expected)));
    EXPECT_TRUE(s->check_sat().is_unsat())
        << term << " can differ from " << expected;
    s->pop();
  }

  SmtSolver s;
  /** The sort of the arguments, which each subclass makes */
  Sort sort;
  std::size_t next_symbol = 0;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(BoolNaryTests);
class BoolNaryTests : public NaryTests
{
 protected:
  void SetUp() override
  {
    NaryTests::SetUp();
    sort = s->make_sort(BOOL);
  }
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(IntNaryTests);
class IntNaryTests : public NaryTests
{
 protected:
  void SetUp() override
  {
    NaryTests::SetUp();
    sort = s->make_sort(INT);
  }
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(RealNaryTests);
class RealNaryTests : public NaryTests
{
 protected:
  void SetUp() override
  {
    NaryTests::SetUp();
    sort = s->make_sort(REAL);
  }
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(BVNaryTests);
class BVNaryTests : public NaryTests
{
 protected:
  void SetUp() override
  {
    NaryTests::SetUp();
    sort = s->make_sort(BV, 8);
  }
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(StrNaryTests);
class StrNaryTests : public NaryTests
{
 protected:
  void SetUp() override
  {
    NaryTests::SetUp();
    sort = s->make_sort(STRING);
  }
};

TEST_P(BoolNaryTests, MakeNaryTerm)
{
  for (PrimOp op : { And, Or, Xor, Implies, Equal, Distinct })
  {
    check(op);
  }
}

TEST_P(BoolNaryTests, MakeNaryTermTooFewArguments)
{
  TermVec args = make_args(sort, 1);
  for (PrimOp op : { And, Implies, Equal, Distinct })
  {
    EXPECT_THROW(make_nary_term(s.get(), op, TermVec{}),
                 IncorrectUsageException)
        << to_string(op);
    EXPECT_THROW(make_nary_term(s.get(), op, args), IncorrectUsageException)
        << to_string(op);
  }
}

TEST_P(IntNaryTests, MakeNaryTerm)
{
  for (PrimOp op :
       { Plus, Minus, Mult, IntDiv, Lt, Le, Gt, Ge, Equal, Distinct })
  {
    check(op);
  }
}

TEST_P(RealNaryTests, MakeNaryTerm)
{
  for (PrimOp op : { Minus, Div, Lt })
  {
    check(op);
  }
}

TEST_P(BVNaryTests, MakeNaryTerm)
{
  for (PrimOp op : { BVAnd, BVOr, BVXor, BVAdd, BVMul, Equal, Distinct })
  {
    check(op);
  }
}

TEST_P(StrNaryTests, MakeNaryTerm)
{
  for (PrimOp op : { StrConcat, StrLt, StrLeq })
  {
    check(op);
  }
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverVariadicOpsTests,
    BoolNaryTests,
    testing::ValuesIn(available_non_generic_solver_configurations()),
    ConfigName());

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverVariadicOpsTests,
    IntNaryTests,
    testing::ValuesIn(filter_non_generic_solver_configurations({ THEORY_INT })),
    ConfigName());

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverVariadicOpsTests,
    RealNaryTests,
    testing::ValuesIn(
        filter_non_generic_solver_configurations({ THEORY_REAL })),
    ConfigName());

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverVariadicOpsTests,
    BVNaryTests,
    testing::ValuesIn(filter_non_generic_solver_configurations({ THEORY_BV })),
    ConfigName());

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverVariadicOpsTests,
    StrNaryTests,
    testing::ValuesIn(filter_non_generic_solver_configurations({ THEORY_STR })),
    ConfigName());

}  // namespace
