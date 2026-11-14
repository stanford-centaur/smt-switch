/*!
 * \file unit-term-visitor.cpp
 * \brief Tests the read-only term visitor
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>

#include <string>

#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/solver_factory.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"
#include "smt-switch/term_visitor.h"

using namespace smt;

namespace {

/** Records the terms it visits, skipping below skip_at and stopping at
 *  abort_at
 */
class RecordingVisitor : public smt::TermVisitor
{
 public:
  TermVec visited;
  Term skip_at;
  Term abort_at;

 protected:
  VisitResult visit_term(const Term & term) override
  {
    visited.push_back(term);
    if (term == abort_at)
    {
      return VisitResult::Abort;
    }
    if (term == skip_at)
    {
      return VisitResult::Skip;
    }
    return VisitResult::Continue;
  }
};

/** Names a case after its solver, e.g. CVC5 */
struct SolverName
{
  std::string operator()(const testing::TestParamInfo<SolverEnum> & info) const
  {
    return to_string(info.param);
  }
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(TermVisitor);
class TermVisitor : public ::testing::TestWithParam<SolverEnum>
{
 protected:
  void SetUp() override
  {
    // a logging solver keeps the terms as built, children in order
    s = create_solver(GetParam(), /* logging */ true);
    Sort bvsort = s->make_sort(BV, 8);
    x = s->make_symbol("x", bvsort);
    y = s->make_symbol("y", bvsort);
    z = s->make_symbol("z", bvsort);
    a = s->make_term(BVAdd, x, y);
    b = s->make_term(BVAdd, y, z);
    f = s->make_term(BVMul, a, b);
  }
  SmtSolver s;
  Term x, y, z, a, b, f;
};

TEST_P(TermVisitor, VisitsEachSubtermOnceInPreOrder)
{
  RecordingVisitor v;
  v.visit(f);
  EXPECT_EQ(v.visited, (TermVec{ f, b, z, y, a, x }));
}

TEST_P(TermVisitor, SkipLeavesOutTheChildren)
{
  RecordingVisitor v;
  v.skip_at = b;
  v.visit(f);
  EXPECT_EQ(v.visited, (TermVec{ f, b, a, y, x }));
}

TEST_P(TermVisitor, AbortStopsTheWalk)
{
  RecordingVisitor v;
  v.abort_at = b;
  v.visit(f);
  EXPECT_EQ(v.visited, (TermVec{ f, b }));
}

TEST_P(TermVisitor, RemembersEarlierVisits)
{
  RecordingVisitor v;
  v.visit(a);
  v.visit(f);
  EXPECT_EQ(v.visited, (TermVec{ a, y, x, f, b, z }));
}

INSTANTIATE_TEST_SUITE_P(,
                         TermVisitor,
                         testing::ValuesIn(available_solver_enums()),
                         SolverName());

}  // namespace
