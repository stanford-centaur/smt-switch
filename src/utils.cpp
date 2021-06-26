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
  Sort sort = cnf->get_sort();
  assert(sort->get_sort_kind() == BOOL);
  if (cnf->is_value() && cnf->to_string() == "true")
  {  // empty cnf formula
    y << "p cnf 0 0\n";
    return;
  }
  TermVec before_and_elimination({ cnf });
  TermVec after_and_elimination;
  // This while loop separate the clauses, after_and_elimination will contain
  // all clauses because every smt::and op will be eliminated. This happens
  // because until smt::and op is not detected that term is added back to
  // before_and_elimination, and as no term with smt::or as the primOp is
  // touched all clauses shall be separated and be intact
  while (!before_and_elimination.empty())
  {
    Term t = before_and_elimination.back();
    before_and_elimination.pop_back();
    smt::Op op = t->get_op();
    assert(op.is_null() || op == smt::Or || op == smt::And || op == smt::Not);
    if (op.prim_op == smt::And)
    {
      for (auto u : t)
      {
        before_and_elimination.push_back(u);
      }
    }
    else
    {
      after_and_elimination.push_back(t);
    }
  }
  // Storing literals from each clause, each vector in clauses will contain the
  // literals from a clause
  std::vector<std::vector<Term>> clauses;

  for (auto u : after_and_elimination)
  {
    std::vector<Term> after_or_elimination;
    std::vector<Term> before_or_elimination({ u });
    while (!before_or_elimination.empty())
    {  // This while loop functions in the same way as above and eliminates
       // smt::or by separating the literals
      Term t = before_or_elimination.back();
      before_or_elimination.pop_back();
      smt::Op op = t->get_op();
      assert(op.is_null() || op == smt::Or || op == smt::Not);

      if(op.prim_op == smt::Or)
      {
        for(auto u : t)
        {
          before_or_elimination.push_back(u);
        }
      }
      else
      {
        assert(op.is_null() || op == smt::Not);
        after_or_elimination.push_back(t);
      }
    }
    clauses.push_back(after_or_elimination);
   }

   std::map<Term, int> ma;  // This map will create a mapping from symbols to
                            // distinct contiguous integer values.
   int ptr = 0;  // pointer to store the next integer used in mapping

   // iterating within each clause and mapping every distinct symbol to a
   // natural number
   for (auto u : clauses)
   {
     for (auto uu : u)
     {  // Using literals from all the clauses to create the mapping
       if (uu->is_value() && uu->to_string() == "false")
       {  // For an empty clause, which will just contain the term "false"
       }
       else if (uu->is_symbolic_const())
       {  // A positive literal
         if (ma.find(uu) == ma.end())
         {  // Checking if symbol is absent in the mapping done till now
           ptr++;
           ma[uu] = ptr;
         }
       }
       else
       {  // A negative literal
         Term t = (*(uu->begin()));
         if (ma.find(t) == ma.end())
         {
           ptr++;
           ma[t] = ptr;
         }
       }
     }
   }
   //printing the output in DIMACS format
   y << "p cnf ";
   y << ptr;  // number of distinct symbols
   y << " ";

   int sz = clauses.size();

   y << sz;  // number of clauses
   y << "\n";

   // iterating within each clause and assigning the literal their mapped
   // value(for a positive literal) or it's negative value(for a negative
   // literal)
   for (auto u : clauses)
   {
     for (auto uu : u)
     {
       if (uu->is_value() && uu->to_string() == "false")
       {  // For an empty clause
       }
       else if (uu->is_symbolic_const())
       {
         y << (ma[uu]);  // Positive number for a positive literal
         y << " ";
       }
       else
       {
         Term t = (*(uu->begin()));
         y << ((-(ma[t])));  // Negative number for a negative literal
         y << " ";
       }
     }
     y << 0;  // Symbolizing end of line
     y << "\n";
  }
}




Term term_gen(SmtSolver s, Sort boolsort, int& pt){
  return (s->make_symbol("x"+std::to_string(pt++), boolsort));
}


  

Term to_cnf(Term formula, SmtSolver s, Sort boolsort){
  srand(time(NULL));
  std::map<Term, Term>ma;//map ma contains the mapping of each term to it's new symbol in tseytin's transformation
  
  //returning symbolic constants directly
  if(formula->is_symbolic_const()){
    return formula;
  }
  //This vector is going to be broken down into it's symbolic constants, as we need to know which symbols have already been used so that we don't create symbols with the same name
  


  static int pt=1;// a pointer which will decide the next symbols name
  
  TermVec vec={formula};//vec stores the formulas which yet need to be given a symbolic name
  //reduced stores (c) <-> (a op b). (c) as the first term of the pair and (a op b) as the second term in the pair
  std::vector<std::pair<Term, Term>>reduced;
  bool fir=0;//If fir is true it mean's we have named the parent formula i.e the formula given to us
  Term parent;//parent will contain the symbolic name of the parent formula
  while(!vec.empty()){
    Term u=vec.back();
    vec.pop_back();
    smt::Op op=u->get_op();
    if(op==smt::And || op==smt::Or || op==smt::Xor || op==smt::Implies){

      Term mid;//The symbolic name of "u" will be stored in mid
      if(ma.find(u)!=ma.end()){//if the subformula is already named we assign it it's name given
        mid=ma[u];
      }
      else{//procedure to create a new symbolic name
        mid=term_gen(s, boolsort, pt);
        ma[u]=mid;
      }
      //naming the parent formula 
      if(fir==0){
        fir=1;//signalling that parent formula has been named
        parent=mid;
      }

      auto it=u->begin();
      Term le=(*it);
      it++;
      Term ri=(*it);
      Term le_new=le;//The symbolic name of the left child
      Term ri_new=ri;//The symbolic name of the right child
      if(!(le->is_symbolic_const())){
        if(ma.find(le)!=ma.end()){
          le_new=ma[le];
        }
        else{
          le_new=term_gen(s, boolsort, pt);
          ma[le]=le_new;
        }
      }
      if(!(ri->is_symbolic_const())){
        if(ma.find(ri)!=ma.end()){
          ri_new=ma[ri];
        }
        else{
          ri_new=term_gen(s, boolsort, pt);
          ma[ri]=ri_new;
        }
      }
      //pushing a pair of c, (a op b) where c is mid, a is le_new and b is ri_new, the new symbolic expressions(or their original symbols if they were originally symbolic constants)
      reduced.push_back({mid, s->make_term(op, le_new, ri_new)});
      if(!(le->is_symbolic_const())){
        vec.push_back(le);//adding back to vec, to break down further
      }
      if(!(ri->is_symbolic_const())){
        vec.push_back(ri);//adding back to vec, to break down further
      }
    }
    else if(op==smt::Not){ //Works in the same way as the if statement above
      Term t=(*u->begin());
      Term mid;
      if(ma.find(u)!=ma.end()){
        mid=ma[u];
      }
      else{
        mid=term_gen(s, boolsort, pt);
        ma[u]=mid;
      }
      if(fir==0){
        fir=1;
        parent=mid;
      }
      if(t->is_symbolic_const()){
        reduced.push_back({mid, s->make_term(Not, t)});
      }
      else{
        Term le;
        if(ma.find(t)!=ma.end()){
          le=ma[t];
        }
        else{
          le=term_gen(s, boolsort, pt);
          ma[t]=le;
        }
        reduced.push_back({mid, s->make_term(Not, le)});
        vec.push_back(t);
      }
    }
  }

  TermVec clauses;
  

  for(auto u:reduced){
    Term fi=u.first;
    Term se=u.second;
    smt::Op op=se->get_op();

    if(op==smt::And){//((~a) v (~b) v (c)) and ((a) v (~c)) and ((b) v (~c))
      auto it=(se->begin());
      Term le=(*it);
      it++;
      Term ri=(*it);
      clauses.push_back(s->make_term(Or, s->make_term(Or, s->make_term(Not, le), s->make_term(Not, ri)), fi));
      clauses.push_back(s->make_term(Or, le, s->make_term(Not, fi)));
      clauses.push_back(s->make_term(Or, ri, s->make_term(Not, fi)));
    }
    else if(op==smt::Or){//((a) v (b) v (~c)) and ((~a) v c) and ((~b) v c)
      auto it=(se->begin());
      Term le=(*it);
      it++;
      Term ri=(*it);
      clauses.push_back(s->make_term(Or, s->make_term(Or, le, ri), s->make_term(Not, fi)));
      clauses.push_back(s->make_term(Or, s->make_term(Not, le), fi));
      clauses.push_back(s->make_term(Or, s->make_term(Not, ri), fi));
    }
    else if(op==smt::Xor){//((~a) v (~b) v (~c)) and ((a) v (b) v (~c)) and ((c) v (b) v (~a)) and ((c) v (a) v (~b))
      auto it=(se->begin());
      Term le=(*it);
      it++;
      Term ri=(*it);
      clauses.push_back(s->make_term(Or, s->make_term(Or, s->make_term(Not, le), s->make_term(Not, ri)), s->make_term(Not, fi)));
      clauses.push_back(s->make_term(Or, s->make_term(Or, le, ri), s->make_term(Not, fi)));
      clauses.push_back(s->make_term(Or, s->make_term(Or, fi, ri), s->make_term(Not, le)));
      clauses.push_back(s->make_term(Or, s->make_term(Or, fi, le), s->make_term(Not, ri)));
    }
    else if(op==smt::Implies){//((~a) v (b) v (~c)) and ((a) v (c)) and ((~b) v (c))
      auto it=(se->begin());
      Term le=(*it);
      it++;
      Term ri=(*it);
      clauses.push_back(s->make_term(Or, s->make_term(Or, s->make_term(Not, le), ri), s->make_term(Not, fi)));
      clauses.push_back(s->make_term(Or, le, fi));
      clauses.push_back(s->make_term(Or, s->make_term(Not, ri), fi));
    }
    else{//((~a) v (~c)) and ((a) v (c))
      Term le=(*(se->begin()));
      clauses.push_back(s->make_term(Or, s->make_term(Not, le), s->make_term(Not, fi)));
      clauses.push_back(s->make_term(Or, le, fi));  
    }
  }
  //taking the and of all clauses generated to create the cnf
  for(int i=1; i<clauses.size(); i++){
    clauses[0]=s->make_term(And, clauses[0], clauses[i]);
  }
  //taking and of the cnf with the symbolic term of the entire formula 
  clauses[0]=s->make_term(And, parent, clauses[0]);
  
  return clauses[0];
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
