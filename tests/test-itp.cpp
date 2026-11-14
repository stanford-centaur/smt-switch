/*!
 * \file test-itp.cpp
 * \brief Tests for interpolant generation
 * \author Makai Mann
 * \author Áron Ricardo Perez-Lopez
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <cstddef>
#include <memory>
#include <ostream>
#include <sstream>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

#include "available_solvers.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/interpolator.h"
#include "smt-switch/ops.h"
#include "smt-switch/printing_interpolator.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/solver_factory.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"
#include "smt-switch/term_translator.h"
#include "smt-switch/utils.h"

using namespace smt;
using namespace smt_tests;
using namespace std;

namespace {

// an interpolator, and the theory it interpolates in: THEORY_INT or
// THEORY_BV
struct ItpParam
{
  SolverConfiguration config;
  SolverAttribute theory;
};

ostream & operator<<(ostream & o, const ItpParam & p)
{
  return o << p.config << " over " << p.theory;
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(ItpTests);
class ItpTests : public ::testing::Test,
                 public ::testing::WithParamInterface<ItpParam>
{
 protected:
  void SetUp() override
  {
    itp = create_interpolator(GetParam().config.solver_enum);

    // the queries order the symbols, so unsigned bit-vector comparisons
    // keep them unsatisfiable
    if (GetParam().theory == THEORY_INT)
    {
      sort = itp->make_sort(INT);
      lt = Lt;
      gt = Gt;
    }
    else
    {
      sort = itp->make_sort(BV, 8);
      lt = BVUlt;
      gt = BVUgt;
    }
    x = itp->make_symbol("x", sort);
    y = itp->make_symbol("y", sort);
    z = itp->make_symbol("z", sort);
    w = itp->make_symbol("w", sort);
  }
  SmtInterpolator itp;
  Sort sort;
  PrimOp lt, gt;
  Term x, y, z, w;
};

TEST_P(ItpTests, Interpolant)
{
  Term A = itp->make_term(lt, x, y);
  A = itp->make_term(And, A, itp->make_term(lt, y, w));

  Term B = itp->make_term(gt, z, w);
  B = itp->make_term(And, B, itp->make_term(lt, z, x));

  Term I;
  Result r = itp->get_interpolant(A, B, I);
  ASSERT_TRUE(r.is_unsat());

  UnorderedTermSet free_symbols;
  get_free_symbolic_consts(I, free_symbols);

  EXPECT_EQ(free_symbols.count(y), 0);
  EXPECT_EQ(free_symbols.count(z), 0);
}

// Expects interpolants, from an interpolator of the given kind, to be a
// sequence interpolant of formulae: a chain, as get_sequence_interpolants
// promises. A regular solver of the same backend checks each implication,
// in the logic given if one is.
void expect_chain(SolverEnum interpolator,
                  const TermVec & formulae,
                  const TermVec & interpolants,
                  const string & query,
                  const string & logic = "")
{
  ASSERT_EQ(interpolants.size(), formulae.size() - 1) << query;
  SmtSolver checker = create_solver(
      SolverConfiguration(interpolator_base_solver(interpolator), false));
  checker->set_opt("incremental", "true");
  if (!logic.empty())
  {
    checker->set_logic(logic);
  }
  TermTranslator to_checker(checker);
  TermVec f, I;
  for (const Term & t : formulae)
  {
    f.push_back(to_checker.transfer_term(t));
  }
  for (size_t i = 0; i < interpolants.size(); ++i)
  {
    ASSERT_TRUE(interpolants[i]) << query << ", split " << i;
    I.push_back(to_checker.transfer_term(interpolants[i]));
  }
  auto inconsistent = [&checker](const Term & a, const Term & b) {
    checker->push();
    checker->assert_formula(a);
    checker->assert_formula(b);
    bool unsat = checker->check_sat().is_unsat();
    checker->pop();
    return unsat;
  };
  EXPECT_TRUE(inconsistent(f.front(), checker->make_term(Not, I.front())))
      << query << ": the first formula does not imply " << interpolants.front();
  for (size_t i = 1; i < I.size(); ++i)
  {
    EXPECT_TRUE(inconsistent(checker->make_term(And, I[i - 1], f[i]),
                             checker->make_term(Not, I[i])))
        << query << ": " << interpolants[i - 1] << " and formula " << i
        << " do not imply " << interpolants[i];
  }
  EXPECT_TRUE(inconsistent(I.back(), f.back()))
      << query << ": " << interpolants.back()
      << " is consistent with the last formula";
}

TEST_P(ItpTests, SequenceInterpolants)
{
  // A1 : x < y /\ y < w
  Term A1 = itp->make_term(lt, x, y);
  A1 = itp->make_term(And, A1, itp->make_term(lt, y, w));

  // A2 : z > w /\ z < x
  Term A2 = itp->make_term(gt, z, w);
  A2 = itp->make_term(And, A2, itp->make_term(lt, z, x));

  // A3 : y > z /\ y < w
  Term A3 = itp->make_term(gt, y, z);
  A3 = itp->make_term(And, A3, itp->make_term(lt, y, w));

  TermVec formulae({ A1, A2, A3 });
  TermVec interpolants;

  Result r = itp->get_sequence_interpolants(formulae, interpolants);
  ASSERT_TRUE(r.is_unsat());
  expect_chain(
      GetParam().config.solver_enum, formulae, interpolants, "A1, A2, A3");
}

// A bounded model checking unrolling: a and b start at 0, each step
// increments one of them, and after k steps a + b exceeds k.
TEST_P(ItpTests, SequenceInterpolantsOfAnUnrolling)
{
  PrimOp add = GetParam().theory == THEORY_INT ? Plus : BVAdd;
  // cvc5 takes a while for the deeper bit-vector unrollings
  bool cvc5_bv = GetParam().config.solver_enum == CVC5_INTERPOLATOR
                 && GetParam().theory == THEORY_BV;
  int max_k = cvc5_bv ? 3 : 5;
  for (int k = 2; k <= max_k; ++k)
  {
    SmtInterpolator s = create_interpolator(GetParam().config.solver_enum);
    Sort srt = GetParam().theory == THEORY_INT ? s->make_sort(INT)
                                               : s->make_sort(BV, 8);
    Term one = s->make_term(1, srt);
    TermVec a, b;
    for (int i = 0; i <= k; ++i)
    {
      a.push_back(s->make_symbol("a" + std::to_string(i), srt));
      b.push_back(s->make_symbol("b" + std::to_string(i), srt));
    }
    Term zero = s->make_term(0, srt);
    TermVec formulae{ s->make_term(And,
                                   s->make_term(Equal, a[0], zero),
                                   s->make_term(Equal, b[0], zero)) };
    for (int i = 0; i < k; ++i)
    {
      Term step_a = s->make_term(
          And,
          s->make_term(Equal, a[i + 1], s->make_term(add, a[i], one)),
          s->make_term(Equal, b[i + 1], b[i]));
      Term step_b = s->make_term(
          And,
          s->make_term(Equal, b[i + 1], s->make_term(add, b[i], one)),
          s->make_term(Equal, a[i + 1], a[i]));
      formulae.push_back(s->make_term(Or, step_a, step_b));
    }
    formulae.push_back(
        s->make_term(gt, s->make_term(add, a[k], b[k]), s->make_term(k, srt)));
    TermVec interpolants;
    ASSERT_TRUE(s->get_sequence_interpolants(formulae, interpolants).is_unsat())
        << "k = " << k;
    expect_chain(GetParam().config.solver_enum,
                 formulae,
                 interpolants,
                 "k = " + std::to_string(k));
  }
}

TEST_P(ItpTests, ReportsItsSolverEnum)
{
  EXPECT_EQ(itp->get_solver_enum(), GetParam().config.solver_enum);
}

TEST_P(ItpTests, RefusesSolvingCalls)
{
  Term t = itp->make_term(lt, x, y);
  EXPECT_THROW(itp->push(), IncorrectUsageException);
  EXPECT_THROW(itp->pop(), IncorrectUsageException);
  EXPECT_THROW(itp->pop_all(), IncorrectUsageException);
  EXPECT_THROW(itp->assert_formula(t), IncorrectUsageException);
  EXPECT_THROW(itp->check_sat(), IncorrectUsageException);
  EXPECT_THROW(itp->check_sat_assuming(TermVec{ t }), IncorrectUsageException);
  EXPECT_THROW(itp->get_value(x), IncorrectUsageException);
  Term const_base;
  EXPECT_THROW(itp->get_array_values(x, const_base), IncorrectUsageException);
  UnorderedTermSet assumptions;
  EXPECT_THROW(itp->get_unsat_assumptions(assumptions),
               IncorrectUsageException);
}

// an interpolation query uses the backend's own context levels, which must
// not show through
TEST_P(ItpTests, ContextLevelStaysZero)
{
  Term A =
      itp->make_term(And, itp->make_term(lt, x, y), itp->make_term(lt, y, z));
  Term B = itp->make_term(gt, x, z);
  Term I;
  ASSERT_TRUE(itp->get_interpolant(A, B, I).is_unsat());
  EXPECT_EQ(itp->get_context_level(), 0);
}

TEST_P(ItpTests, RefusesTurningInterpolationOff)
{
  EXPECT_THROW(itp->set_opt("produce-interpolants", "false"),
               IncorrectUsageException);
  Term A =
      itp->make_term(And, itp->make_term(lt, x, y), itp->make_term(lt, y, z));
  Term I;
  EXPECT_TRUE(itp->get_interpolant(A, itp->make_term(gt, x, z), I).is_unsat());
  EXPECT_TRUE(I);
}

TEST_P(ItpTests, InterpolatesAfterReset)
{
  // a reset before first use as well as after a query; each round makes its
  // own symbols, since terms from before a reset belong to the old instance
  itp->reset();
  for (int round = 0; round < 2; ++round)
  {
    Sort s = GetParam().theory == THEORY_INT ? itp->make_sort(INT)
                                             : itp->make_sort(BV, 8);
    Term a = itp->make_symbol("a", s);
    Term b = itp->make_symbol("b", s);
    Term c = itp->make_symbol("c", s);
    Term A =
        itp->make_term(And, itp->make_term(lt, a, b), itp->make_term(lt, b, c));
    Term I;
    EXPECT_TRUE(itp->get_interpolant(A, itp->make_term(gt, a, c), I).is_unsat())
        << "round " << round;
    EXPECT_TRUE(I) << "round " << round;
    itp->reset();
  }
}

// The same queries with and without reusing formulas between them answer the
// same; the queries extend and repeat each other, share prefixes, and shrink
// and reorder them.
TEST_P(ItpTests, ReuseKeepsResults)
{
  for (const char * incremental : { "true", "false" })
  {
    SmtInterpolator s = create_interpolator(GetParam().config.solver_enum);
    s->set_opt("incremental", incremental);
    Sort srt = GetParam().theory == THEORY_INT ? s->make_sort(INT)
                                               : s->make_sort(BV, 8);
    Term a = s->make_symbol("a", srt);
    Term b = s->make_symbol("b", srt);
    Term c = s->make_symbol("c", srt);
    Term d = s->make_symbol("d", srt);
    Term t1 = s->make_term(lt, d, a);
    Term t2 = s->make_term(And, s->make_term(lt, a, b), s->make_term(lt, a, c));
    Term t3 = s->make_term(lt, b, d);
    Term t4 = s->make_term(lt, c, d);
    // each query but the last is unsat
    std::vector<TermVec> queries{ { t1, t2, t3 },     { t1, t2, t3, t4 },
                                  { t1, t2, t3, t4 }, { t1, t2, t4 },
                                  { t1, t2, t4, t3 }, { t2, t1, t3 },
                                  { t2, t1 } };
    for (std::size_t q = 0; q < queries.size(); ++q)
    {
      TermVec itps;
      Result r = s->get_sequence_interpolants(queries[q], itps);
      bool unsat_expected = q + 1 < queries.size();
      EXPECT_TRUE(unsat_expected ? r.is_unsat() : r.is_sat())
          << "incremental " << incremental << ", query " << q << ": " << r;
      if (!unsat_expected)
      {
        continue;
      }
      ASSERT_EQ(itps.size(), queries[q].size() - 1)
          << "incremental " << incremental << ", query " << q;
      // an interpolant mentions only symbols on both sides of its split
      for (std::size_t i = 0; i < itps.size(); ++i)
      {
        UnorderedTermSet before, after, in_itp;
        for (std::size_t k = 0; k < queries[q].size(); ++k)
        {
          get_free_symbolic_consts(queries[q][k], k <= i ? before : after);
        }
        get_free_symbolic_consts(itps[i], in_itp);
        for (const Term & sym : in_itp)
        {
          EXPECT_TRUE(before.count(sym) && after.count(sym))
              << "incremental " << incremental << ", query " << q << ", split "
              << i << ": " << sym;
        }
      }
      expect_chain(GetParam().config.solver_enum,
                   queries[q],
                   itps,
                   std::string("incremental ") + incremental + ", query "
                       + std::to_string(q));
    }
  }
}

TEST_P(ItpTests, IncrementalCanChangeBetweenQueries)
{
  Term A =
      itp->make_term(And, itp->make_term(lt, x, y), itp->make_term(lt, y, z));
  Term B = itp->make_term(gt, x, z);
  for (const char * value : { "true", "false" })
  {
    EXPECT_NO_THROW(itp->set_opt("incremental", value)) << value;
    Term I;
    EXPECT_TRUE(itp->get_interpolant(A, B, I).is_unsat()) << value;
  }
}

// reset turns incremental back on, as it is at startup; that shows in what
// a printing interpolator writes, as it follows what the one it wraps reuses
TEST_P(ItpTests, ResetTurnsIncrementalBackOn)
{
  auto log_after_reset = [this](bool turn_off) {
    std::ostringstream out;
    SmtInterpolator s = create_printing_interpolator(
        create_interpolator(GetParam().config.solver_enum), &out);
    if (turn_off)
    {
      s->set_opt("incremental", "false");
    }
    s->reset();
    std::size_t start = out.str().size();
    // the terms made before the reset are gone, so these come after it
    Sort srt = GetParam().theory == THEORY_INT ? s->make_sort(INT)
                                               : s->make_sort(BV, 8);
    Term a = s->make_symbol("a", srt);
    Term b = s->make_symbol("b", srt);
    Term c = s->make_symbol("c", srt);
    TermVec query{ s->make_term(lt, a, b),
                   s->make_term(lt, b, c),
                   s->make_term(lt, c, a) };
    // the second query extends the first, so it may reuse what that kept
    for (int round = 0; round < 2; ++round)
    {
      TermVec itps;
      EXPECT_TRUE(s->get_sequence_interpolants(query, itps).is_unsat())
          << "round " << round;
      query.push_back(s->make_term(lt, a, c));
    }
    return out.str().substr(start);
  };
  EXPECT_EQ(log_after_reset(true), log_after_reset(false));
}

TEST_P(ItpTests, InterpolatesAfterResetAssertions)
{
  Term A =
      itp->make_term(And, itp->make_term(lt, x, y), itp->make_term(lt, y, z));
  Term B = itp->make_term(gt, x, z);
  // a reset before the first query as well as after one
  itp->reset_assertions();
  for (int round = 0; round < 2; ++round)
  {
    Term I;
    EXPECT_TRUE(itp->get_interpolant(A, B, I).is_unsat()) << "round " << round;
    EXPECT_TRUE(I) << "round " << round;
    itp->reset_assertions();
  }
}

TEST_P(ItpTests, AnswersEachQuery)
{
  Term up =
      itp->make_term(And, itp->make_term(lt, x, y), itp->make_term(lt, y, z));
  Term down =
      itp->make_term(And, itp->make_term(gt, x, y), itp->make_term(gt, y, z));
  Term contradiction =
      itp->make_term(And, itp->make_term(gt, z, y), itp->make_term(gt, y, z));
  // unsat queries, including ones with a side unsat on its own
  for (auto [A, B] : { std::pair{ up, itp->make_term(gt, x, z) },
                       std::pair{ down, itp->make_term(lt, x, z) },
                       std::pair{ contradiction, itp->make_term(lt, x, z) },
                       std::pair{ down, contradiction } })
  {
    Term I;
    EXPECT_TRUE(itp->get_interpolant(A, B, I).is_unsat()) << A << " / " << B;
    EXPECT_TRUE(I) << A << " / " << B;
  }
  // a satisfiable query has no interpolant
  Term I;
  EXPECT_TRUE(itp->get_interpolant(down, itp->make_term(gt, x, z), I).is_sat());
}

TEST_P(ItpTests, SequenceInterpolantsRefuseMisuse)
{
  Term t = itp->make_term(lt, x, y);
  TermVec out{ t };
  EXPECT_THROW(itp->get_sequence_interpolants({ t, t }, out),
               IncorrectUsageException);
  out.clear();
  EXPECT_THROW(itp->get_sequence_interpolants({ t }, out),
               IncorrectUsageException);
}

TEST_P(ItpTests, RefusesNonBooleanAndNullFormulae)
{
  Term t = itp->make_term(lt, x, y);
  Term I;
  EXPECT_THROW(itp->get_interpolant(x, t, I), IncorrectUsageException);
  EXPECT_THROW(itp->get_interpolant(t, Term(), I), IncorrectUsageException);
  TermVec out;
  EXPECT_THROW(itp->get_sequence_interpolants({ t, Term() }, out),
               IncorrectUsageException);
}

TEST_P(ItpTests, PrintingWritesNoRefusedQuery)
{
  std::ostringstream out;
  SmtInterpolator s = create_printing_interpolator(
      create_interpolator(GetParam().config.solver_enum), &out);
  Sort srt =
      GetParam().theory == THEORY_INT ? s->make_sort(INT) : s->make_sort(BV, 8);
  Term a = s->make_symbol("a", srt);
  Term b = s->make_symbol("b", srt);
  Term a_lt_b = s->make_term(lt, a, b);
  std::size_t start = out.str().size();
  Term I;
  EXPECT_THROW(s->get_interpolant(a_lt_b, a, I), IncorrectUsageException);
  TermVec itps;
  EXPECT_THROW(s->get_sequence_interpolants({ a_lt_b, b }, itps),
               IncorrectUsageException);
  EXPECT_EQ(out.str().substr(start), "");
}

// a refused query keeps none of its formulae, nor those of the query before,
// for the next one
TEST_P(ItpTests, RefusedNonBooleanFormulaLeavesNoAssertionBehind)
{
  Term x_lt_y = itp->make_term(lt, x, y);
  Term y_lt_x = itp->make_term(lt, y, x);
  TermVec itps;
  EXPECT_TRUE(
      itp->get_sequence_interpolants({ x_lt_y, y_lt_x }, itps).is_unsat());
  itps.clear();
  EXPECT_THROW(itp->get_sequence_interpolants({ x_lt_y, x }, itps),
               IncorrectUsageException);
  itps.clear();
  EXPECT_TRUE(
      itp->get_sequence_interpolants({ y_lt_x, itp->make_term(lt, y, z) }, itps)
          .is_sat());
}

// an interpolator holds no assertions, so there is nothing to dump
TEST_P(ItpTests, RefusesDumping)
{
  EXPECT_THROW(itp->dump_smt2(testing::TempDir() + "itp.smt2"),
               IncorrectUsageException);
}

// no interpolator passes incremental on to its solver, so the log does not
// show it, but the wrapped interpolator still takes it and checks it
TEST_P(ItpTests, PrintingKeepsIncrementalOutOfTheLog)
{
  std::ostringstream out;
  SmtInterpolator printing = create_printing_interpolator(itp, &out);
  printing->set_opt("incremental", "false");
  EXPECT_EQ(out.str().find(":incremental"), std::string::npos) << out.str();
  EXPECT_THROW(printing->set_opt("incremental", "maybe"),
               IncorrectUsageException);
}

// a printing interpolator leaves the answer to the one it wraps
TEST_P(ItpTests, PrintedSequenceInterpolantsFormAChain)
{
  std::ostringstream out;
  SmtInterpolator printing = create_printing_interpolator(itp, &out);
  Term A1 =
      itp->make_term(And, itp->make_term(lt, x, y), itp->make_term(lt, y, w));
  Term A2 =
      itp->make_term(And, itp->make_term(gt, z, w), itp->make_term(lt, z, x));
  Term A3 =
      itp->make_term(And, itp->make_term(gt, y, z), itp->make_term(lt, y, w));
  TermVec formulae{ A1, A2, A3 };
  TermVec interpolants;
  ASSERT_TRUE(
      printing->get_sequence_interpolants(formulae, interpolants).is_unsat());
  expect_chain(
      GetParam().config.solver_enum, formulae, interpolants, "A1, A2, A3");
}

TEST_P(ItpTests, InterpolatesWithAnArrayOnOneSide)
{
  // a[z] = x and a[z] > y on one side, x < y on the other: a and z are not
  // shared, so the interpolant mentions only x and y
  Term a = itp->make_symbol("a", itp->make_sort(ARRAY, sort, sort));
  Term read = itp->make_term(Select, a, z);
  Term with_array = itp->make_term(
      And, itp->make_term(Equal, read, x), itp->make_term(gt, read, y));
  Term without_array = itp->make_term(lt, x, y);
  UnorderedTermSet shared{ x, y };
  for (auto [A, B] :
       { pair{ with_array, without_array }, pair{ without_array, with_array } })
  {
    Term I;
    ASSERT_TRUE(itp->get_interpolant(A, B, I).is_unsat()) << A << " / " << B;
    UnorderedTermSet free_symbols;
    get_free_symbolic_consts(I, free_symbols);
    for (const Term & symbol : free_symbols)
    {
      EXPECT_TRUE(shared.count(symbol)) << I << " mentions " << symbol;
    }
    expect_chain(GetParam().config.solver_enum, { A, B }, { I }, "A, B");
  }
}

TEST_P(ItpTests, InterpolatesOverASharedArray)
{
  if (GetParam().config.solver_enum == YICES2_INTERPOLATOR)
  {
    GTEST_SKIP() << "the Yices2 interpolator fixes each shared symbol to its "
                    "value in a model, which MCSAT cannot do for an array";
  }
  // a[z] = x on one side and a[z] < x on the other, which share all three
  Term a = itp->make_symbol("a", itp->make_sort(ARRAY, sort, sort));
  Term read = itp->make_term(Select, a, z);
  Term A = itp->make_term(Equal, read, x);
  Term B = itp->make_term(lt, read, x);
  Term I;
  ASSERT_TRUE(itp->get_interpolant(A, B, I).is_unsat());
  expect_chain(GetParam().config.solver_enum, { A, B }, { I }, "A, B");
}

TEST_P(ItpTests, NonlinearInterpolant)
{
  if (GetParam().theory != THEORY_INT)
  {
    GTEST_SKIP() << "a square is never negative only over the integers";
  }
  if (GetParam().config.solver_enum == MSAT_INTERPOLATOR)
  {
    GTEST_SKIP() << "MathSAT answers unknown to nonlinear integer arithmetic";
  }
  // x * x is never negative, so y = x * x cannot be, whatever x is
  Term A = itp->make_term(Equal, y, itp->make_term(Mult, x, x));
  Term B = itp->make_term(Lt, y, itp->make_term(0, sort));
  Term I;
  Result r = itp->get_interpolant(A, B, I);
  ASSERT_TRUE(r.is_unsat()) << r;
  UnorderedTermSet free_symbols;
  get_free_symbolic_consts(I, free_symbols);
  EXPECT_EQ(free_symbols.count(x), 0u) << I;
  // a regular Yices2 solves nonlinear arithmetic only in a nonlinear logic
  expect_chain(
      GetParam().config.solver_enum, { A, B }, { I }, "A, B", "QF_NIA");
}

// each interpolator runs the tests in every theory it supports
vector<ItpParam> itp_params()
{
  vector<ItpParam> params;
  for (SolverAttribute theory : { THEORY_INT, THEORY_BV })
  {
    for (SolverConfiguration sc :
         filter_interpolator_configurations({ theory }))
    {
      params.push_back({ sc, theory });
    }
  }
  return params;
}

// names a case after its solver and theory, e.g. CVC5_INT or BZLA_BV
string itp_param_name(const testing::TestParamInfo<ItpParam> & info)
{
  string solver = to_string(info.param.config.solver_enum);
  solver = solver.substr(0, solver.find("_INTERPOLATOR"));
  string theory = to_string(info.param.theory);
  theory = theory.substr(theory.find("THEORY_") + 7);
  string name = solver + "_" + theory;
  if (info.param.config.is_logging_solver)
  {
    name += "_LOGGING";
  }
  return name;
}

INSTANTIATE_TEST_SUITE_P(,
                         ItpTests,
                         testing::ValuesIn(itp_params()),
                         itp_param_name);
}  // namespace
