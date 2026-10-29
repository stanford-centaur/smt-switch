/*********************                                                        */
/*! \file yices2-polynomial.cpp
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief
**
**
**/

#include <gmp.h>  // IWYU pragma: keep (required by yices.h)
#include <gtest/gtest.h>
#include <yices.h>

#include <memory>
#include <string>

#include "exceptions.h"
#include "smt_defs.h"
#include "term.h"
#include "yices2_factory.h"
#include "yices2_term.h"

using namespace smt;

/* A Yices term that no smt-switch op describes has to say so. A null op
 * would make it a leaf, which whoever rebuilds the term from its children
 * believes. Yices' ceiling is one such term, and since nothing in
 * smt-switch reaches it, it has to be built through the Yices API here.
 */
TEST(Yices2Polynomial, AnUnmappedConstructorRefusesToReportAnOp)
{
  SmtSolver s = Yices2SolverFactory::create(false);
  term_t ceiling = yices_ceil(yices_new_uninterpreted_term(yices_real_type()));
  ASSERT_NE(ceiling, NULL_TERM);

  Term unmapped = std::make_shared<Yices2Term>(ceiling);
  EXPECT_THROW(unmapped->get_op(), NotImplementedException);
}
