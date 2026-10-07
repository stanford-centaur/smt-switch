/*!
 * \file term_utils.h
 * \brief What a term has to match after a round trip through a solver.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * A LoggingSolver records the smt-switch term it was given, so whatever a
 * walker or a translator reads back out of it has to be that same term. A
 * native solver keeps its own representation and is free to normalize, so
 * the most that can be asked of it is a term meaning the same thing.
 * Conflating the two either lets a logging solver lose the input or excludes
 * every solver that rewrites.
 */

#pragma once

#include <gtest/gtest.h>

#include "available_solvers.h"
#include "smt.h"

namespace smt_tests {

/** Checks a term read back out of a solver against the one put in: the same
 *  term for a logging solver, which records its input, and a term that means
 *  the same for a non-logging one, which may have rewritten it.
 *
 *  Equivalence is decided by enumerating every assignment to the free
 *  symbols where their sorts are small and finite and the solver folds a
 *  ground term to a value, which answers the question from constant folding
 *  rather than putting it to the solver that did the rewriting. Where that
 *  does not apply the solver is asked instead, by asserting the two terms
 *  distinct; that constraint stays asserted, since `push` needs an
 *  incremental solver and not every test asks for one, so a call that can
 *  reach it has to be a test's last check.
 *
 *  Use with EXPECT_TRUE or ASSERT_TRUE.
 *
 *  @param config the configuration of the solver the term passed through,
 *         which for a translation is the one it was transferred into
 *  @param solver the solver both terms belong to
 *  @param read_back the term that came back out
 *  @param original the term that went in
 */
::testing::AssertionResult round_trip_matches(
    const SolverConfiguration & config,
    const smt::SmtSolver & solver,
    const smt::Term & read_back,
    const smt::Term & original);

}  // namespace smt_tests
