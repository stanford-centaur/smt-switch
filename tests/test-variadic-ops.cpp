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
#include "smt-switch/sort.h"

namespace smt::tests {

namespace {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(VariadicOpsTests);
class VariadicOpsTests : public testing::Test,
                         public testing::WithParamInterface<SolverConfiguration>
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

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverVariadicOpsTests,
                         VariadicOpsTests,
                         testing::ValuesIn(available_solver_configurations()));

/** Checks a backend's applications of an operator to more than two arguments
 *  against the applications to two that SMT-LIB defines them as, whether the
 *  solver applies the operator to more arguments itself or the backend builds
 *  them from applications to two.
 */
class NaryTests : public testing::Test,
                  public testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("incremental", "true");
  }

  /** Expects the applications of op to three and to four arguments of sort,
   *  and to three through the overload taking three, to be equal in every
   *  model to the applications to two that SMT-LIB defines them as
   */
  void check(PrimOp op)
  {
    SCOPED_TRACE(to_string(op));
    try
    {
      TermVec args = make_args(sort, 4);
      expect_equivalent(s->make_term(op, args), from_binary(op, args));
      args.pop_back();
      expect_equivalent(s->make_term(op, args), from_binary(op, args));
      expect_equivalent(s->make_term(op, args[0], args[1], args[2]),
                        from_binary(op, args));
    }
    catch (std::exception & e)
    {
      ADD_FAILURE() << e.what();
    }
  }

  /** The application of op to args, three or more, as SMT-LIB defines it
   *  from applications to two: folded from the right for =>, the
   *  conjunction of the applications to each pair for distinct, of those to
   *  each argument and the next for the :chainable operators, and folded
   *  from the left for the rest, which are :left-assoc
   */
  Term from_binary(PrimOp op, const TermVec & args)
  {
    std::size_t n = args.size();
    if (op == Implies)
    {
      Term result = args[n - 1];
      for (std::size_t i = n - 1; i > 0; --i)
      {
        result = s->make_term(op, args[i - 1], result);
      }
      return result;
    }
    TermVec conjuncts;
    if (op == Distinct)
    {
      for (std::size_t i = 0; i < n; ++i)
      {
        for (std::size_t j = i + 1; j < n; ++j)
        {
          conjuncts.push_back(s->make_term(op, args[i], args[j]));
        }
      }
    }
    else if (op == Equal || op == Lt || op == Le || op == Gt || op == Ge
             || op == StrLt || op == StrLeq)
    {
      for (std::size_t i = 0; i + 1 < n; ++i)
      {
        conjuncts.push_back(s->make_term(op, args[i], args[i + 1]));
      }
    }
    else
    {
      Term result = args[0];
      for (std::size_t i = 1; i < n; ++i)
      {
        result = s->make_term(op, result, args[i]);
      }
      return result;
    }
    Term conjunction = conjuncts[0];
    for (std::size_t i = 1; i < conjuncts.size(); ++i)
    {
      conjunction = s->make_term(And, conjunction, conjuncts[i]);
    }
    return conjunction;
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

TEST_P(BoolNaryTests, MatchesSmtLibDefinition)
{
  for (PrimOp op : { And, Or, Xor, Implies, Equal, Distinct })
  {
    check(op);
  }
}

TEST_P(BoolNaryTests, OneArgument)
{
  TermVec args = make_args(sort, 1);
  for (PrimOp op : { And, Implies, Equal, Distinct })
  {
    EXPECT_THROW(s->make_term(op, args), IncorrectUsageException)
        << to_string(op);
  }
}

TEST_P(IntNaryTests, MatchesSmtLibDefinition)
{
  for (PrimOp op :
       { Plus, Minus, Mult, IntDiv, Lt, Le, Gt, Ge, Equal, Distinct })
  {
    check(op);
  }
}

TEST_P(RealNaryTests, MatchesSmtLibDefinition)
{
  for (PrimOp op : { Minus, Div, Lt })
  {
    check(op);
  }
}

TEST_P(BVNaryTests, MatchesSmtLibDefinition)
{
  for (PrimOp op : { BVAnd, BVOr, BVXor, BVAdd, BVMul, Equal, Distinct })
  {
    check(op);
  }
}

TEST_P(StrNaryTests, MatchesSmtLibDefinition)
{
  for (PrimOp op : { StrConcat, StrLt, StrLeq })
  {
    check(op);
  }
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverVariadicOpsTests,
                         BoolNaryTests,
                         testing::ValuesIn(available_solver_configurations()),
                         ConfigName());

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverVariadicOpsTests,
                         IntNaryTests,
                         testing::ValuesIn(filter_solver_configurations(
                             { SolverAttribute::THEORY_INT })),
                         ConfigName());

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverVariadicOpsTests,
                         RealNaryTests,
                         testing::ValuesIn(filter_solver_configurations(
                             { SolverAttribute::THEORY_REAL })),
                         ConfigName());

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverVariadicOpsTests,
                         BVNaryTests,
                         testing::ValuesIn(filter_solver_configurations(
                             { SolverAttribute::THEORY_BV })),
                         ConfigName());

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverVariadicOpsTests,
                         StrNaryTests,
                         testing::ValuesIn(filter_solver_configurations(
                             { SolverAttribute::THEORY_STR })),
                         ConfigName());

}  // namespace

}  // namespace smt::tests
