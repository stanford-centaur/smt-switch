/*!
 * \file unsat_core_reducer.cpp
 * \brief Reducer that shrinks unsatisfiable sets of assumptions
 * \author Ahmed Irfan
 * \author Hongce Zhang
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/unsat_core_reducer.h"

#include <algorithm>
#include <cstddef>
#include <memory>
#include <random>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/result.h"
#include "smt-switch/solver.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

namespace smt {

UnsatCoreReducer::UnsatCoreReducer(SmtSolver reducer_solver)

    : reducer_(reducer_solver), to_reducer_(reducer_solver)
{
  reducer_->set_opt("produce-unsat-assumptions", "true");
  reducer_->set_opt("incremental", "true");
}

bool UnsatCoreReducer::reduce_assump_unsatcore(const Term & formula,
                                               const TermVec & assump,
                                               TermVec & out_red,
                                               TermVec * out_rem,
                                               unsigned iter,
                                               unsigned rand_seed)
{
  TermVec bool_assump, local_assump;
  UnorderedTermMap to_ext_assump;
  TermVec cand_res;
  for (const auto & a : assump)
  {
    Term t = to_reducer_.transfer_term(a);
    cand_res.push_back(t);
    to_ext_assump[t] = a;
  }

  reducer_->push();
  reducer_->assert_formula(to_reducer_.transfer_term(formula));

  // exit if the formula is unsat without assumptions.
  Result r = reducer_->check_sat();
  if (r.is_unsat())
  {
    reducer_->pop();
    return true;
  }

  if (rand_seed > 0)
  {
    shuffle(cand_res.begin(),
            cand_res.end(),
            std::default_random_engine(rand_seed));
  }

  for (const auto & a : cand_res)
  {
    Term l = label(a);
    reducer_->assert_formula(reducer_->make_term(Op::Implies, l, a));
    bool_assump.push_back(l);
  }

  unsigned cur_iter = 0;
  bool first_iter = true;
  // iter == 0 interpreted as allowing unlimited iterations
  // iter != 0 restricts to iter iterations
  while (!iter || cur_iter < iter)
  {
    cur_iter += 1;
    r = reducer_->check_sat_assuming(bool_assump);

    if (first_iter && r.is_sat())
    {
      reducer_->pop();
      return false;
    }

    if (!r.is_unsat())
    {
      reducer_->pop();
      throw SolverException("reduce_assump_unsatcore expected unsat but got "
                            + r.to_string());
    }

    bool_assump.clear();
    local_assump.clear();

    UnorderedTermSet core_set;
    reducer_->get_unsat_assumptions(core_set);
    for (const auto & a : cand_res)
    {
      Term l = label(a);
      if (core_set.find(l) != core_set.end())
      {
        local_assump.push_back(a);
        bool_assump.push_back(l);
      }
      else if (out_rem)
      {
        // add the removed assumption in the out_rem (after translating to the
        // external solver)
        out_rem->push_back(to_ext_assump.at(a));
      }
    }

    if (local_assump.size() == cand_res.size())
    {
      break;
    }
    else
    {
      cand_res = local_assump;
    }

    first_iter = false;
  }

  reducer_->pop();

  // copy the result
  for (const auto & a : cand_res)
  {
    out_red.push_back(to_ext_assump.at(a));
  }

  return true;
}

bool UnsatCoreReducer::linear_reduce_assump_unsatcore(const Term & formula,
                                                      const TermVec & assump,
                                                      TermVec & out_red,
                                                      TermVec * out_rem,
                                                      unsigned iter)
{
  TermVec bool_assump;
  UnorderedTermMap to_ext_assump;
  TermVec cand_res;
  for (const auto & a : assump)
  {
    Term t = to_reducer_.transfer_term(a);
    // A repeated assumption gets the same label twice, and removing one
    // copy at a time never shrinks the core.
    if (!to_ext_assump.emplace(t, a).second)
    {
      throw IncorrectUsageException("linear_reduce_assump_unsatcore got "
                                    + a->to_string() + " more than once");
    }
    cand_res.push_back(t);
  }

  reducer_->push();
  reducer_->assert_formula(to_reducer_.transfer_term(formula));

  // exit if the formula is unsat without assumptions.
  Result r = reducer_->check_sat();
  if (r.is_unsat())
  {
    reducer_->pop();
    return true;
  }

  UnorderedTermMap label_to_cand_;
  for (const auto & a : cand_res)
  {
    Term l = label(a);
    reducer_->assert_formula(reducer_->make_term(Op::Implies, l, a));
    bool_assump.push_back(l);
    label_to_cand_.emplace(l, a);
  }

  unsigned cur_iter = 0;
  std::size_t assump_pos_for_removal = 0;
  r = reducer_->check_sat_assuming(bool_assump);
  if (r.is_sat())
  {
    reducer_->pop();
    return false;
  }
  if (!r.is_unsat())
  {
    reducer_->pop();
    throw SolverException(
        "linear_reduce_assump_unsatcore expected unsat but got "
        + r.to_string());
  }

  while (cur_iter <= iter && assump_pos_for_removal < bool_assump.size())
  {
    cur_iter = iter > 0 ? cur_iter + 1 : cur_iter;

    TermVec bool_assump_for_query;
    bool_assump_for_query.reserve(bool_assump.size() - 1);
    for (std::size_t idx = 0; idx < bool_assump.size(); ++idx)
    {
      if (idx != assump_pos_for_removal)
        bool_assump_for_query.push_back(bool_assump.at(idx));
    }

    r = reducer_->check_sat_assuming(bool_assump_for_query);
    if (r.is_sat())
    {
      // we cannot remove this assumption, then try next one
      ++assump_pos_for_removal;
    }
    else if (!r.is_unsat())
    {
      reducer_->pop();
      throw SolverException(
          "linear_reduce_assump_unsatcore expected unsat but got "
          + r.to_string());
    }
    else
    {
      // we can remove this assumption

      // the reason of using unsat core rather than the removal
      // of bool_assump[bool_assump_for_query] is because
      // the core could be even smaller
      UnorderedTermSet core_set;
      reducer_->get_unsat_assumptions(core_set);
      {  // remove those not in core_set from bool_assump
        TermVec new_bool_assump;
        new_bool_assump.reserve(core_set.size());
        for (const auto & l : bool_assump)
        {
          if (core_set.find(l) != core_set.end()) new_bool_assump.push_back(l);
        }
        bool_assump.swap(
            new_bool_assump);  // do "bool_assump = new_bool_assump" w.o. copy
      }
      // we don't need to change assump_pos_for_removal, because the size of
      // bool_assump is reduced by at least one, so in the next round
      // it is another element sitting at this location
    }  // end of the unsat case
    // at this point, bool_assump should be the output
  }

  for (const auto & l : bool_assump)
  {
    const Term & a = label_to_cand_.at(l);
    out_red.push_back(to_ext_assump.at(a));
  }

  // in the case that we don't need the removed ones
  // we don't have to iterate through the constraint vector
  if (out_rem)
  {
    UnorderedTermSet remaining_labels(bool_assump.begin(), bool_assump.end());
    for (const auto & a : cand_res)
    {
      Term l = label(a);
      if (remaining_labels.find(l) == remaining_labels.end())
      {
        // add the removed assumption in the out_rem (after translating to the
        // external solver)
        out_rem->push_back(to_ext_assump.at(a));
      }
    }  // for each in cand_res
  }  // if (out_red)

  reducer_->pop();

  return true;
}

void UnsatCoreReducer::clear_term_translation_cache()
{
  to_reducer_.get_cache().clear();
}

Term UnsatCoreReducer::label(const Term & t)
{
  auto it = labels_.find(t);
  if (it != labels_.end())
  {
    return labels_.at(t);
  }

  unsigned i = 0;
  Term l;
  while (true)
  {
    try
    {
      l = reducer_->make_symbol(
          "assump_" + std::to_string(t->hash()) + "_" + std::to_string(i),
          reducer_->make_sort(SortKind::BOOL));
      break;
    }
    catch (IncorrectUsageException & e)
    {
      ++i;
    }
  }

  labels_[t] = l;
  return l;
}

}  // namespace smt
