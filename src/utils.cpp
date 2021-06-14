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

#include <algorithm>
#include <map>
#include <random>
#include <sstream>
#include <string>

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

void get_matching_terms(const smt::Term & term,
                    smt::UnorderedTermSet & out,
                    bool (*matching_fun)(const smt::Term & term))
{
  smt::TermVec to_visit({ term });
  smt::UnorderedTermSet visited;

  smt::Term t;
  while (to_visit.size()) {
    t = to_visit.back();
    to_visit.pop_back();

    if (visited.find(t) == visited.end()) {
      visited.insert(t);

      if (matching_fun(t))
      {
        out.insert(t);
      }
      else
      {  // add children to queue
        for (auto tt : t) {
          to_visit.push_back(tt);
        }
      }
    }
  }
}

void get_free_symbolic_consts(const smt::Term & term,
                              smt::UnorderedTermSet & out)
{
  auto f = [](const smt::Term & t) { return t->is_symbolic_const(); };
  get_matching_terms(term, out, f);
}

void get_free_symbols(const smt::Term & term, smt::UnorderedTermSet & out)
{
  auto f = [](const smt::Term & t) { return t->is_symbol(); };
  get_matching_terms(term, out, f);
}

void get_ops(const smt::Term & term, smt::UnorderedOpSet & out)
{
  smt::TermVec to_visit({ term });
  smt::UnorderedTermSet visited;

  smt::Term t;
  while (to_visit.size()) {
    t = to_visit.back();
    to_visit.pop_back();
    if (visited.find(t) == visited.end()) {
      visited.insert(t);
      Op op = t->get_op();
      // Only add non-null operators to the set
      if (!op.is_null()) {
        out.insert(t->get_op());
        // add children to queue
        for (auto tt : t) {
          to_visit.push_back(tt);
        }
      }
    }
  }
}

bool is_lit(const Term & l, const Sort & boolsort)
{
  // take a boolsort as an argument for sort aliasing solvers
  if (l->get_sort() != boolsort)
  {
    return false;
  }

  if (l->is_symbolic_const())
  {
    return true;
  }

  Op op = l->get_op();
  // check both for sort aliasing solvers
  if (op == Not || op == BVNot)
  {
    Term first_child = *(l->begin());
    return first_child->is_symbolic_const();
  }

  return false;
}

void cnf_to_dimacs(Term cnf, std::ostringstream & y)
{
  if (cnf->is_value() && cnf->to_string() == "true")
  {  // empty cnf formula
    y << "p cnf 0 0\n";
    return;
  }
  TermVec vecs({ cnf });
  TermVec vecs2;
  // This while loop separate the clauses, vecs2 will contain all clauses
  // because every smt::and op will be eliminated. This happens because until
  // smt::and op is not detected that term is added back to vecs, and as no term
  // with smt::or as the primOp is touched all clauses shall be separated and be
  // intact
  while (!vecs.empty())
  {
    Term t = vecs.back();
    vecs.pop_back();
    smt::Op op = t->get_op();
    if (op.prim_op == smt::And)
    {
      for (auto u : t)
      {
        vecs.push_back(u);
      }
    }
    else
    {
      vecs2.push_back(t);
    }
  }
  // Storing literals from each clause, each vector in literals will contain the
  // literals from a clause
  std::vector<std::vector<Term>> literals;

  for (auto u : vecs2)
  {
    std::vector<Term>add;
    std::vector<Term>le({u});
    while (!le.empty())
    {  // This while loop functions in the same way as above and eliminates
       // smt::or by separating the literals
      Term t=le.back();
      le.pop_back();
      smt::Op op=t->get_op();
      if(op.prim_op==smt::Or){
        for(auto u:t){
          le.push_back(u);
        }
      }
      else{
        add.push_back(t);
      }
    }
    literals.push_back(add);
   }

   std::map<std::string, int>
       ma;  // This map will create a mapping from symbols to distinct
            // contiguous integer values.
   int ptr = 0;  // pointer to store the next integer used in mapping

   for(auto u:literals){
     for (auto uu : u)
     {  // Using literals from all the clauses to create the mapping
       if (uu->is_value())
       {  // For an empty clause, which will just contain the term "false"
       }
       else if (uu->is_symbolic_const())
       {  // A positive literal
         if (ma.find(uu->to_string()) == ma.end())
         {  // Checking if symbol is absent in the mapping done till now
           ptr++;
           ma[uu->to_string()] = ptr;
         }
       }
       else
       {  // A negative literal
         Term t = (*(uu->begin()));
         if (ma.find(t->to_string()) == ma.end())
         {
           ptr++;
           ma[t->to_string()] = ptr;
         }
       }
     }
   }
   //printing the output in DIMACS format
   y << "p cnf ";
   y << ptr;  // number of distinct symbols
   y << " ";

   int sz=literals.size();

   y << sz;  // number of clauses
   y << "\n";

   for (auto u : literals)
   {
     for (auto uu : u)
     {
       if (uu->is_value())
       {  // For an empty clause
       }
       else if (uu->is_symbolic_const())
       {
         y << (ma[uu->to_string()]);  // Positive number for a positive literal
         y << " ";
       }
       else
       {
         Term t = (*(uu->begin()));
         y << ((
             -(ma[t->to_string()])));  // Negative number for a negative literal
         y << " ";
       }
     }
     y << 0;  // Symbolizing end of line
     y << "\n";
  }
}

// ----------------------------------------------------------------------------

UnsatCoreReducer::UnsatCoreReducer(SmtSolver reducer_solver)

  : reducer_(reducer_solver),
    to_reducer_(reducer_solver)
{
  reducer_->set_opt("produce-unsat-assumptions", "true");
  reducer_->set_opt("incremental", "true");
}

UnsatCoreReducer::~UnsatCoreReducer()
{
}

bool UnsatCoreReducer::reduce_assump_unsatcore(const Term &formula,
                                               const TermVec &assump,
                                               TermVec &out_red,
                                               TermVec *out_rem,
                                               unsigned iter,
                                               unsigned rand_seed)
{
  TermVec bool_assump, local_assump;
  UnorderedTermMap to_ext_assump;
  TermVec cand_res;
  for (const auto & a : assump) {
    Term t = to_reducer_.transfer_term(a);
    cand_res.push_back(t);
    to_ext_assump[t] = a;
  }

  reducer_->push();
  reducer_->assert_formula(to_reducer_.transfer_term(formula));

  // exit if the formula is unsat without assumptions.
  Result r = reducer_->check_sat();
  if (r.is_unsat()) {
    reducer_->pop();
    return true;
  }

  if (rand_seed > 0) {
    shuffle(cand_res.begin(), cand_res.end(),
            std::default_random_engine(rand_seed));
  }

  for (const auto & a : cand_res) {
    Term l = label(a);
    reducer_->assert_formula(reducer_->make_term(Implies, l, a));
    bool_assump.push_back(l);
  }

  unsigned cur_iter = 0;
  bool first_iter = true;
  while (cur_iter <= iter) {
    cur_iter = iter > 0 ? cur_iter+1 : cur_iter;
    r = reducer_->check_sat_assuming(bool_assump);

    if (first_iter && r.is_sat()) {
      reducer_->pop();
      return false;
    }

    assert(r.is_unsat());

    bool_assump.clear();
    local_assump.clear();

    UnorderedTermSet core_set;
    reducer_->get_unsat_assumptions(core_set);
    for (const auto & a : cand_res) {
      Term l = label(a);
      if (core_set.find(l) != core_set.end()) {
        local_assump.push_back(a);
        bool_assump.push_back(l);
      } else if (out_rem) {
        // add the removed assumption in the out_rem (after translating to the
        // external solver)
        out_rem->push_back(to_ext_assump.at(a));
      }
    }

    if (local_assump.size() == cand_res.size()) {
      break;
    } else {
      cand_res = local_assump;
    }

    first_iter = false;
  }

  reducer_->pop();

  // copy the result
  for (const auto &a : cand_res) {
    out_red.push_back(to_ext_assump.at(a));
  }

  return true;
}

bool UnsatCoreReducer::linear_reduce_assump_unsatcore(
                              const smt::Term &formula,
                              const smt::TermVec &assump,
                              smt::TermVec &out_red,
                              smt::TermVec *out_rem,
                              unsigned iter)
{
  TermVec bool_assump;
  UnorderedTermMap to_ext_assump;
  TermVec cand_res;
  for (const auto & a : assump) {
    Term t = to_reducer_.transfer_term(a);
    cand_res.push_back(t);
    to_ext_assump[t] = a;
  }

  reducer_->push();
  reducer_->assert_formula(to_reducer_.transfer_term(formula));

  // exit if the formula is unsat without assumptions.
  Result r = reducer_->check_sat();
  if (r.is_unsat()) {
    reducer_->pop();
    return true;
  }

  UnorderedTermMap label_to_cand_;
  for (const auto & a : cand_res) {
    Term l = label(a);
    reducer_->assert_formula(reducer_->make_term(Implies, l, a));
    bool_assump.push_back(l);
    label_to_cand_.emplace(l, a);
  }

  unsigned cur_iter = 0;
  size_t assump_pos_for_removal = 0;
  r = reducer_->check_sat_assuming(bool_assump);
  if (r.is_sat()) {
    reducer_->pop();
    return false;
  }
  assert(r.is_unsat());

  while (cur_iter <= iter && assump_pos_for_removal < bool_assump.size()) {
    cur_iter = iter > 0 ? cur_iter+1 : cur_iter;

    TermVec bool_assump_for_query;
    bool_assump_for_query.reserve(bool_assump.size()-1);
    for (size_t idx = 0; idx < bool_assump.size(); ++ idx) {
      if (idx != assump_pos_for_removal)
        bool_assump_for_query.push_back(bool_assump.at(idx));
    }

    r = reducer_->check_sat_assuming(bool_assump_for_query);
    if (r.is_sat()) {
      // we cannot remove this assumption, then try next one
      ++ assump_pos_for_removal;
    } else {
      // we can remove this assumption
      assert(r.is_unsat());

      // the reason of using unsat core rather than the removal
      // of bool_assump[bool_assump_for_query] is because
      // the core could be even smaller
      UnorderedTermSet core_set;
      reducer_->get_unsat_assumptions(core_set);
      { // remove those not in core_set from bool_assump
        TermVec new_bool_assump;
        new_bool_assump.reserve(core_set.size());
        for (const auto & l : bool_assump) {
          if (core_set.find(l) != core_set.end())
            new_bool_assump.push_back(l);
        }
        bool_assump.swap(new_bool_assump); // do "bool_assump = new_bool_assump" w.o. copy
      }
      assert(!bool_assump.empty());
      assert(bool_assump.size() <= bool_assump_for_query.size());
      // we don't need to change assump_pos_for_removal, because the size of
      // bool_assump is reduced by at least one, so in the next round
      // it is another element sitting at this location
    } // end of the unsat case
    // at this point, bool_assump should be the output
  }

  for (const auto & l : bool_assump) {
    const Term & a = label_to_cand_.at(l);
    out_red.push_back(to_ext_assump.at(a));
  }

  // in the case that we don't need the removed ones
  // we don't have to iterate through the constraint vector
  if (out_rem) {
    UnorderedTermSet remaining_labels(bool_assump.begin(), bool_assump.end());
    for (const auto & a : cand_res) {
      Term l = label(a);
      if (remaining_labels.find(l) == remaining_labels.end()) {
        // add the removed assumption in the out_rem (after translating to the
        // external solver)
        out_rem->push_back(to_ext_assump.at(a));
      }
    } // for each in cand_res
  } // if (out_red)

  reducer_->pop();

  return true;
}

Term UnsatCoreReducer::label(const Term & t)
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

// ----------------------------------------------------------------------------

DisjointSet::DisjointSet(bool (*c)(const smt::Term & a, const smt::Term & b))
    : comp(c)
{
}

DisjointSet::~DisjointSet() {}

void DisjointSet::add(const Term & a, const Term & b)
{
  if (leader_.find(a) != leader_.end())
  {
    Term leadera = leader_.at(a);
    UnorderedTermSet & groupa = group_.at(leadera);

    if (leader_.find(b) != leader_.end())
    {
      Term leaderb = leader_.at(b);

      if (leadera != leaderb)
      {
        UnorderedTermSet & groupb = group_.at(leaderb);

        if (comp(leadera, leaderb))
        {
          // Choose according to the given ranking
          groupa.insert(groupb.begin(), groupb.end());

          for (const Term & t : groupb)
          {
            leader_[t] = leadera;
          }
          groupb.clear();
          group_.erase(leaderb);
        }
        else
        {
          groupb.insert(groupa.begin(), groupa.end());

          for (const Term & t : groupa)
          {
            leader_[t] = leaderb;
          }
          groupa.clear();
          group_.erase(leadera);
        }
      }
    }
    else
    {
      groupa.insert(b);
      leader_[b] = leadera;
    }
  }
  else if (leader_.find(b) != leader_.end())
  {
    Term leaderb = leader_.at(b);
    group_[leaderb].insert(a);
    leader_[a] = leaderb;
  }
  else
  {
    // Choose according to the given Ranking
    if (comp(a, b))
    {
      leader_[a] = a;
      leader_[b] = a;
      group_[a] = UnorderedTermSet({ a, b });
    }
    else
    {
      assert(!b->is_value());
      leader_[a] = b;
      leader_[b] = b;
      group_[b] = UnorderedTermSet({ a, b });
    }
  }
}

Term DisjointSet::find(const Term & t) const
{
  assert(leader_.find(t) != leader_.end());
  return leader_.at(t);
}

void DisjointSet::clear()
{
  leader_.clear();
  group_.clear();
}

}  // namespace smt
