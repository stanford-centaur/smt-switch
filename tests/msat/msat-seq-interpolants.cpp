/*********************                                                        */
/*! \file msat-seq-interpolants.cpp
** \verbatim
** Top contributors (to current version):
**   Po-Chun Chien
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

#include <gtest/gtest.h>

#include <memory>
#include <vector>

#include "msat_factory.h"
#include "smt.h"
// after a full installation
// #include "smt-switch/msat_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;

void check_itp_seq(const SmtSolver s,
                   const TermVec & formulas,
                   const bool expect_sat = false)
{
  TermVec itp_seq;
  Result r = s->get_sequence_interpolants(formulas, itp_seq);
  EXPECT_EQ(r.is_unsat(), !expect_sat);
}

TEST(MsatSeqInterpolants, GetSequenceInterpolants)
{
  SmtSolver s = MsatSolverFactory::create_interpolating_solver();
  Sort intsort = s->make_sort(INT);

  Term w = s->make_symbol("w", intsort);
  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term z = s->make_symbol("z", intsort);

  Term t1 = s->make_term(Lt, w, x);  // w < x
  Term t2 = s->make_term(
      And, s->make_term(Lt, x, y), s->make_term(Lt, x, z));  // x < y && x < z
  Term t3 = s->make_term(Lt, y, w);                          // y < w
  Term t4 = s->make_term(Lt, z, w);                          // z < w

  // incorrect usage with non-empty itp_seq
  TermVec nonempty_seq = { t1 };
  EXPECT_THROW(s->get_sequence_interpolants({ t1, t2 }, nonempty_seq),
               IncorrectUsageException);

  // incorrect usage with only one input formula
  TermVec itp_seq;
  EXPECT_THROW(s->get_sequence_interpolants({ t1 }, itp_seq),
               IncorrectUsageException);

  check_itp_seq(s, { t1, t2, t3 });
  check_itp_seq(s, { t1, t2, t4 });      // pop 1, push 1
  check_itp_seq(s, { t1, t2, t4, t3 });  // push 1
  check_itp_seq(s, { t2, t1, t3 });      // pop 4, push 3
  check_itp_seq(s, { t2, t1 }, true);    // pop 2 (SAT query)
}
