/*!
 * \file yices2-printing.cpp
 * \brief Tests that a printed Yices2 interpolation query replays.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * The Yices2 interpolator refutes models of B one at a time, so its script
 * is a check of B per model, one of A under it, and a last check of B.
 */

#include <gtest/gtest.h>

#include <ostream>
#include <sstream>

#include "exceptions.h"
#include "exec_utils.h"
#include "interpolating_solver.h"
#include "ops.h"
#include "printing_solver.h"
#include "result.h"
#include "smt_defs.h"
#include "sort.h"
#include "test_paths.h"
#include "yices2_factory.h"

using namespace smt;
using namespace smt_tests;

namespace {

// B has one model, p false, which A refutes, after which B has none
TEST(Yices2InterpolationPrinting, ReplaysEachCheckOfAQuery)
{
  SmtInterpolator itp;
  try
  {
    itp = Yices2SolverFactory::create_interpolating_solver();
  }
  catch (const NotImplementedException & e)
  {
    GTEST_SKIP() << e.what();
  }
  std::stringbuf strbuf;
  std::ostream os(&strbuf);
  SmtInterpolator s = create_printing_interpolator(itp, &os);
  s->set_logic("QF_LIA");
  Term p = s->make_symbol("p", s->make_sort(BOOL));
  Term I;
  ASSERT_TRUE(s->get_interpolant(p, s->make_term(Not, p), I).is_unsat());
  if (smt_tests::yices2_binary.empty())
  {
    GTEST_SKIP() << "configure found no yices-smt2 executable";
  }
  dump_and_run(
      smt_tests::yices2_binary,
      strbuf,
      { { "sat" }, { "((p false))" }, { "unsat" }, { "p" }, { "unsat" } },
      "--mcsat --incremental");
}

}  // namespace
