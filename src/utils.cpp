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

#include <algorithm>
#include <random>

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

// ----------------------------------------------------------------------------

UnsatcoreReducer::UnsatcoreReducer(SmtSolver reducer_solver,
                                   const SmtSolver &ext_solver)
  : reducer_(reducer_solver),
    to_reducer_(ext_solver)
{
}

UnsatcoreReducer::~UnsatcoreReducer()
{
}

void UnsatcoreReducer::reduce_assump_unsatcore(const Term &formula,
                                               const TermVec &assump,
                                               TermVec &out_red,
                                               TermVec *out_rem,
                                               unsigned iter,
                                               unsigned rand_seed)
{
  TermVec bool_assump, tmp_assump;
  UnorderedTermMap to_ext_assump;
  TermVec cand_res;
  for (const auto &a : assump) {
    Term t = to_reducer_.transfer_term(a);
    cand_res.push_back(t);
    to_ext_assump[t] = a;
  }

  reducer_->reset_assertions();
  reducer_->assert_formula(to_reducer_.transfer_term(formula));

  // exit if the formula is unsat without assumptions.
  Result r = reducer_->check_sat();
  if (r.is_unsat()) {
    return;
  }

  if (rand_seed > 0) {
    shuffle(cand_res.begin(), cand_res.end(),
            std::default_random_engine(rand_seed));
  }

  for (auto &a : cand_res) {
    Term l = label(a);
    reducer_->assert_formula(reducer_->make_term(Implies, l, a));
    bool_assump.push_back(l);
  }

  unsigned cur_iter = 0;
  while (cur_iter <= iter) {
    cur_iter = iter > 0 ? cur_iter+1 : cur_iter;
    r = reducer_->check_sat_assuming(bool_assump);
    assert(r.is_unsat());

    bool_assump.clear();
    tmp_assump.clear();

    UnorderedTermSet core_set;
    reducer_->get_unsat_core(core_set);
    for (auto a : cand_res) {
      Term l = label(a);
      if (core_set.find(l) != core_set.end()) {
        tmp_assump.push_back(a);
        bool_assump.push_back(l);
      } else if (out_rem) {
        // add the removed assumption in the out_rem (after translating to the
        // external solver)
        out_rem->push_back(to_ext_assump.at(a));
      }
    }

    if (tmp_assump.size() == cand_res.size()) {
      break;
    } else {
      cand_res = tmp_assump;
    }
  }

  // copy the result
  for (const auto &a : cand_res) {
    out_red.push_back(to_ext_assump.at(a));
  }
}

Term UnsatcoreReducer::label(const Term & t)
{
  auto it = labels_.find(t);
  if (it != labels_.end()) {
    return labels_.at(t);
  }

  unsigned i = 0;
  Term l;
  while (true) {
    try {
      l = reducer_->make_symbol(
          "assump_" + std::to_string(t->hash()) + "_" + std::to_string(i),
          reducer_->make_sort(BOOL));
      break;
    }
    catch (IncorrectUsageException & e) {
      ++i;
    }
    catch (SmtException & e) {
      throw e;
    }
  }

  labels_[t] = l;
  return l;
}

}  // namespace smt
