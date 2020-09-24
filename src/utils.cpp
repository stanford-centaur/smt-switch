/*********************                                                        */
/*! \file utils.cpp
** \verbatim
** Top contributors (to current version):
**   Ahmed Irfan
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Utility functions.
**
**
**/

#include "utils.h"
#include "ops.h"

namespace smt {

void op_partition(smt::PrimOp o,
                  const smt::Term &term, smt::TermVec &out)
{
  smt::TermVec to_visit({ term });
  smt::UnorderedTermSet visited;

  smt::Term t;
  while (to_visit.size()) {
    t = to_visit.back();
    to_visit.pop_back();

    if (visited.find(t) == visited.end()) {
      visited.insert(t);

      smt::Op op = t->get_op();
      if (op.prim_op == o) {
        // add children to queue
        for (auto tt : t) {
          to_visit.push_back(tt);
        }
      } else {
        out.push_back(t);
      }
    }
  }
}

void conjunctive_partition(const smt::Term & term,
                           smt::TermVec & out,
                           bool include_bvand)
{
  if (!include_bvand)
  {
    op_partition(smt::And, term, out);
  }
  else
  {
    TermVec tmp;
    op_partition(smt::And, term, tmp);
    Sort sort;
    for (auto tt : tmp)
    {
      sort = tt->get_sort();
      if (sort->get_sort_kind() == BV && sort->get_width() == 1)
      {
        op_partition(smt::BVAnd, tt, out);
      }
      else
      {
        out.push_back(tt);
      }
    }
  }
}

void disjunctive_partition(const smt::Term & term,
                           smt::TermVec & out,
                           bool include_bvor)
{
  if (!include_bvor)
  {
    op_partition(smt::Or, term, out);
  }
  else
  {
    TermVec tmp;
    op_partition(smt::Or, term, tmp);
    Sort sort;
    for (auto tt : tmp)
    {
      sort = tt->get_sort();
      if (sort->get_sort_kind() == BV && sort->get_width() == 1)
      {
        op_partition(smt::BVOr, tt, out);
      }
      else
      {
        out.push_back(tt);
      }
    }
  }
}

void get_free_symbolic_consts(const smt::Term &term, smt::TermVec &out)
{
  smt::TermVec to_visit({ term });
  smt::UnorderedTermSet visited;

  smt::Term t;
  while (to_visit.size()) {
    t = to_visit.back();
    to_visit.pop_back();

    if (visited.find(t) == visited.end()) {
      visited.insert(t);

      if (t->is_symbolic_const()) {
        out.push_back(t);
      } else {// add children to queue
        for (auto tt : t) {
          to_visit.push_back(tt);
        }
      }
    }
  }
}

}  // namespace smt
