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

#include "identity_walker.h"
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

// mapping each subformula with a new name and returning a vector of pair of
// terms. Each pair consists of the parent term and it's children(for each
// subformula)
class TseitinTraversal : public IdentityWalker
{
 public:
  std::vector<std::pair<Term, Term>>
      reduced;  // stores a pair of (lhs, rhs) in x1(lhs)<->(formula(rhs))

  TseitinTraversal(SmtSolver solver_) : IdentityWalker{ solver_, false } {}
  WalkerStepResult visit_term(Term & term)
  {
    Sort boolsort = term->get_sort();
    assert(term->get_sort() == boolsort);

    auto give_symbolic_name = [&](Term t) {  // producing a new symbol
      int pt = 1;
      while (true)
      {
        try
        {
          return solver_->make_symbol("tseitin_to_cnf_" + std::to_string(pt),
                                      boolsort);
        }
        catch (IncorrectUsageException & e)
        {
          pt++;
        }
      }

    };
    if (!preorder_)  // using post order traversal as I need the new names of
                     // the children to generate the new term
    {
      smt::Op op = term->get_op();
      if (!op.is_null())
      {
        std::vector<Term> vec;  // a vector of all children
        for (auto u : term)
        {
          Term cached_term;
          bool present = query_cache(u,
                                     cached_term);  // finding the new name of
                                                    // each child from the cache
          assert(present == true);
          vec.push_back(cached_term);
        }

        Term term_name = give_symbolic_name(term);  // making a new symbol
        save_in_cache(term, term_name);

        reduced.push_back({ term_name, solver_->make_term(op, vec) });
      }
      else
      {  // mapping a symbolic constant to itself
        save_in_cache(term, term);
      }
    }

    return Walker_Continue;
  }
};

// binarising xor with multiple children
class XorBinarize : public IdentityWalker
{
 public:
  XorBinarize(SmtSolver solver_) : IdentityWalker{ solver_, false } {}
  WalkerStepResult visit_term(Term & term)
  {
    if (!preorder_)
    {
      smt::Op op = term->get_op();
      if (!op.is_null())
      {
        if (op == smt::Xor)
        {
          auto it = term->begin();
          Term cached_term;
          query_cache((*it),
                      cached_term);  // finding the mapped term from the cache
          Term ne = cached_term;
          it++;
          while (it != term->end())
          {  // Binarising the term
            Term cached_term;
            query_cache((*it), cached_term);
            ne = solver_->make_term(op, ne, cached_term);
            it++;
          }
          save_in_cache(term, ne);  // storing the new binarised term in cache
        }
        else
        {
          save_in_cache(term, term);
        }
      }
      else
      {
        save_in_cache(term, term);
      }
    }

    return Walker_Continue;
  }
  Term acc_cache(Term term)
  {
    Term ne;
    query_cache(term, ne);
    return ne;
  }
};

// Given a boolean formula, removes terms "true" and "false" to give a formula
// without adding new symbols

// The way true and false are eliminated is by doing a preorder traversal. When
// I am on a certain node, The children are already reducecd. Reduced means that
// they are a term without true or false, or just true, or just false.
// Inductively this reduction is being maintained till the root node.
class EliminateBooleanConstants : public IdentityWalker
{
 public:
  EliminateBooleanConstants(SmtSolver solver_)
      : IdentityWalker{ solver_, false }
  {
  }
  WalkerStepResult visit_term(Term & term)
  {
    Term tru = solver_->make_term(true);
    Term fal = solver_->make_term(false);
    auto is_true = [&](Term t) {  // If the term is "true"
      return (t == tru);
    };
    auto is_false = [&](Term t) {  // If the term is "false"
      return (t == fal);
    };
    if (!preorder_)
    {
      smt::Op op = term->get_op();
      if (!op.is_null())
      {
        Term tr = solver_->make_term(true);   // Term "true"
        Term fa = solver_->make_term(false);  // Term "false"
        if (op == smt::Not)
        {
          Term t = (*term->begin());
          Term cached_term;
          query_cache(t,
                      cached_term);  // Querying the mapped formula of the child
                                     // as we are doing a preorder traversal

          if (is_true(cached_term))
          {  // not(false)=true
            save_in_cache(term, fa);
          }
          else if (is_false(cached_term))
          {  // not(true)=false
            save_in_cache(term, tr);
          }
          else
          {  // mapping not of the queried term_name.
            save_in_cache(term, solver_->make_term(Not, cached_term));
          }
        }
        else if (op == smt::Equal)
        {
          auto it = term->begin();
          Term le = (*it);
          it++;
          Term ri = (*it);
          // term=(le_name<->ri_name)
          Term le_cached;
          Term ri_cached;
          query_cache(le, le_cached);
          query_cache(ri, ri_cached);
          if ((is_true(le_cached) && is_true(ri_cached))
              || (is_false(le_cached) && is_false(ri_cached)))
          {  //(true==true)=true, (false==false)=true
            save_in_cache(term, tr);
          }
          else if ((is_true(le_cached) && is_false(ri_cached))
                   || (is_false(le_cached) && is_true(ri_cached)))
          {  //(true==false)=false, (false==true)=false
            save_in_cache(term, fa);
          }
          else if (is_true(le_cached))
          {  //(true==ri_name)=ri_name
            save_in_cache(term, ri_cached);
          }
          else if (is_true(ri_cached))
          {  //(le_name==true)=le_name
            save_in_cache(term, le_cached);
          }
          else if (is_false(le_cached))
          {  //(false==ri_name)=not(ri_name)
            save_in_cache(term, solver_->make_term(Not, ri_cached));
          }
          else if (is_false(ri_cached))
          {  //(le_name==false)=not(le_name)
            save_in_cache(term, solver_->make_term(Not, le_cached));
          }
          else
          {  // saving as it is
            save_in_cache(term,
                          solver_->make_term(Equal, le_cached, ri_cached));
          }
        }
        else if (op == smt::Implies)
        {
          auto it = term->begin();
          Term le = (*it);
          it++;
          Term ri = (*it);
          Term le_cached;
          Term ri_cached;
          query_cache(le, le_cached);
          query_cache(ri, ri_cached);
          if (is_false(le_cached) || is_true(ri_cached))
          {  //(false->?)=true, (?->true)=true
            save_in_cache(term, tr);
          }
          else if (is_true(le_cached))
          {  //(true->ri_name)=ri_name
            save_in_cache(term, ri_cached);
          }
          else if (is_false(ri_cached))
          {
            if (is_true(le_cached))
            {  //(true->false)=false
              save_in_cache(term, fa);
            }
            else if (is_false(le_cached))
            {  //(false->false)=true
              save_in_cache(term, tr);
            }
            else
            {  //(le_name->false)=not(le_name)
              save_in_cache(term, solver_->make_term(Not, le_cached));
            }
          }
          else
          {  // saving as it is, as neither lhs or rhs is either "true" or
             // "false"
            save_in_cache(term,
                          solver_->make_term(Implies, le_cached, ri_cached));
          }
        }
        else if (op == smt::And)
        {
          std::vector<Term> vec;  // contains all children which are neither
                                  // "true" nor "false"
          bool false_present = 0;  // false_present=1, if any child is "false"
          auto it = term->begin();
          while (it != term->end())
          {  // iterating over all children
            Term cached_term;
            query_cache((*it), cached_term);
            if (is_true(cached_term))
            {
              it++;
            }
            else if (is_false(cached_term))
            {
              it++;
              false_present = 1;
            }
            else
            {
              it++;
              vec.push_back(cached_term);
            }
          }
          if (false_present)
          {  // if any child is false, the entire expression is false
            save_in_cache(term, fa);
          }
          else if (vec.empty())
          {  // if all children are true, the expression is true
            save_in_cache(term, tr);
          }
          else if (vec.size() == 1)
          {  // if just one child is neither true nor false, that child is
             // equivalent to the entire formula
            save_in_cache(term, vec[0]);
          }
          else
          {  // saving as it is
            save_in_cache(term, solver_->make_term(And, vec));
          }
        }
        else if (op == smt::Or)
        {
          std::vector<Term> vec;  // contains all children which are neither
                                  // "true" nor "false"
          bool true_present = 0;  // true_present=1, if any child is "true"
          auto it = term->begin();
          while (it != term->end())
          {  // iterating over all children
            Term cached_term;
            query_cache((*it), cached_term);
            if (is_true(cached_term))
            {
              true_present = 1;
              it++;
            }
            else if (is_false(cached_term))
            {
              it++;
            }
            else
            {
              it++;
              vec.push_back(cached_term);
            }
          }
          if (true_present)
          {  // any child is "true", implies the entire expression is true
            save_in_cache(term, tr);
          }
          else if (vec.empty())
          {  // If all children are "false", the expression is "false"
            save_in_cache(term, fa);
          }
          else if (vec.size() == 1)
          {  // if just one child is neither true nor false, that child is
             // equivalent to the entire formula
            save_in_cache(term, vec[0]);
          }
          else
          {  // saving as it is
            save_in_cache(term, solver_->make_term(Or, vec));
          }
        }
        else if (op == smt::Xor)
        {
          std::vector<Term> vec;  // contains all children which are neither
                                  // "true" nor "false"
          int true_present =
              0;  // keeping track of number of "true" in the xor expression
          auto it = term->begin();
          while (it != term->end())
          {  // iterating over all children
            Term cached_term;
            query_cache((*it), cached_term);
            if (is_true(cached_term))
            {
              it++;
              true_present++;
            }
            else if (is_false(cached_term))
            {
              it++;
            }
            else
            {
              it++;
              vec.push_back(cached_term);
            }
          }
          if (vec.empty())
          {  // all terms are either "true" or "false"
            if (true_present % 2 == 0)
            {  // even number of "true" implies the expression is false
              save_in_cache(term, fa);
            }
            else
            {  // odd number of "true" implies the expression is false
              save_in_cache(term, tr);
            }
          }
          else if (vec.size() == 1)
          {
            if (true_present % 2 == 0)
            {  // same logic as above, keeping track of the parity of "true"
               // terms
              save_in_cache(term, vec[0]);
            }
            else
            {
              save_in_cache(term, solver_->make_term(Not, vec[0]));
            }
          }
          else
          {
            if (true_present % 2 == 0)
            {
              save_in_cache(term, solver_->make_term(Xor, vec));
            }
            else
            {
              vec[0] = solver_->make_term(
                  Not, vec[0]);  //(Not(x1^x2^x3^x4))=((Not x1)^x2^x3^x4)
              save_in_cache(term, solver_->make_term(Xor, vec));
            }
          }
        }
      }
      else
      {
        save_in_cache(term, term);
      }
    }

    return Walker_Continue;
  }
  Term acc_cache(Term term)
  {
    Term ne;
    query_cache(term, ne);
    return ne;
  }
};

// returns true if the formula is in cnf form else false
bool is_cnf(Term formula)
{
  // similar as cnf_to_dimacs
  // first remove the ands in the outermost layer, then remove the ors from the
  // next level. The remaining terms should be literals
  TermVec before_and_elimination({ formula });
  TermVec after_and_elimination;
  while (!before_and_elimination.empty())
  {
    Term t = before_and_elimination.back();
    before_and_elimination.pop_back();
    smt::Op op = t->get_op();
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
  std::vector<std::vector<Term>> clauses;
  for (auto u : after_and_elimination)
  {
    std::vector<Term> after_or_elimination;
    std::vector<Term> before_or_elimination({ u });
    while (!before_or_elimination.empty())
    {
      Term t = before_or_elimination.back();
      before_or_elimination.pop_back();
      smt::Op op = t->get_op();
      if (op.prim_op == smt::Or)
      {
        for (auto u : t)
        {
          before_or_elimination.push_back(u);
        }
      }
      else
      {
        after_or_elimination.push_back(t);
      }
    }
    clauses.push_back(after_or_elimination);
  }
  bool check = 1;
  for (auto u : clauses)
  {
    for (auto literal : u)
    {
      if (literal->is_symbolic_const())
      {
        continue;
      }
      smt::Op op = literal->get_op();
      if (op == smt::Not && (*(literal->begin()))->is_symbolic_const())
      {
        continue;
      }

      check = 0;  // if the term is not a literal
    }
  }
  return check;
}

Term to_cnf(Term formula, SmtSolver s)
{
  Sort boolsort = formula->get_sort();
  assert(formula->get_sort() == boolsort);
  EliminateBooleanConstants elim(s);
  elim.visit(formula);  // removing "true" and "false" present in formula
  formula = elim.acc_cache(formula);

  if (formula->is_symbolic_const())
  {
    return formula;
  }
  if (formula->to_string() == "false" || formula->to_string() == "true")
  {
    return formula;
  }

  if (is_cnf(formula))  // if the expression is already in cnf just return it
  {
    return formula;
  }

  XorBinarize bin(s);
  bin.visit(formula);  // binarising the formula
  Term formula2 = bin.acc_cache(formula);
  TseitinTraversal obj(s);
  obj.visit(
      formula2);  // traversing the binarised formula to create of pairs of
                  // (c<->(a op b)) which will be used in the transformation

  Term parent = obj.reduced.back().first;

  TermVec clauses;

  // the vector of pairs reduced contains pairs in the form of (c)<->(a op b),
  // where c is the first term of the pair and (a op b) is the second

  for (auto u : obj.reduced)
  {
    Term fi = u.first;
    Term se = u.second;
    smt::Op op = se->get_op();

    if (op == smt::Or)
    {  //(c<->Or(x1, x2, x3, x4....)) = (Or(~c, x1, x2, x3, x4) And (And((c or
       //~x1), (c or ~x2), (c or ~x3), (c or ~x4))
      std::vector<Term> vec;
      std::vector<Term> vec2;
      vec.push_back(s->make_term(Not, fi));
      for (auto u : se)
      {
        vec.push_back(u);
        vec2.push_back(s->make_term(Or, fi, s->make_term(Not, u)));
      }
      clauses.push_back(s->make_term(Or, vec));
      clauses.push_back(s->make_term(And, vec2));
    }
    else if (op == smt::And)
    {  //(c<->And(x1, x2, x3, x4....)) = (Or(c, ~x1, ~x2, ~x3, ~x4) And (And((~c
       // or x1), (~c or x2), (~c or x3), (~c or x4))
      std::vector<Term> vec;
      std::vector<Term> vec2;
      vec.push_back(fi);
      for (auto u : se)
      {
        vec.push_back(s->make_term(Not, u));
        vec2.push_back(s->make_term(Or, u, s->make_term(Not, fi)));
      }
      clauses.push_back(s->make_term(Or, vec));
      clauses.push_back(s->make_term(And, vec2));
    }
    else if (op == smt::Xor)
    {  //((~a) v (~b) v (~c)) and ((a) v (b) v (~c)) and ((c) v (b) v (~a)) and
       //((c) v (a) v (~b))
      auto it = (se->begin());
      Term le = (*it);
      it++;
      Term ri = (*it);
      clauses.push_back(s->make_term(
          Or,
          s->make_term(Or, s->make_term(Not, le), s->make_term(Not, ri)),
          s->make_term(Not, fi)));
      clauses.push_back(
          s->make_term(Or, s->make_term(Or, le, ri), s->make_term(Not, fi)));
      clauses.push_back(
          s->make_term(Or, s->make_term(Or, fi, ri), s->make_term(Not, le)));
      clauses.push_back(
          s->make_term(Or, s->make_term(Or, fi, le), s->make_term(Not, ri)));
    }
    else if (op == smt::Implies)
    {  //((~a) v (b) v (~c)) and ((a) v (c)) and ((~b) v (c))
      auto it = (se->begin());
      Term le = (*it);
      it++;
      Term ri = (*it);
      clauses.push_back(
          s->make_term(Or,
                       s->make_term(Or, s->make_term(Not, le), ri),
                       s->make_term(Not, fi)));
      clauses.push_back(s->make_term(Or, le, fi));
      clauses.push_back(s->make_term(Or, s->make_term(Not, ri), fi));
    }
    else if (op == smt::Equal)
    {  //((~a) v (~b) v (c)) and ((a) v (b) v (c)) and ((~c) v (~b) v (a)) and
       //((c) v (~a) v (b))
      auto it = (se->begin());
      Term le = (*it);
      it++;
      Term ri = (*it);
      clauses.push_back(s->make_term(
          Or,
          s->make_term(Or, s->make_term(Not, le), s->make_term(Not, ri)),
          fi));
      clauses.push_back(s->make_term(Or, s->make_term(Or, le, ri), fi));
      clauses.push_back(
          s->make_term(Or,
                       s->make_term(Or, le, s->make_term(Not, ri)),
                       s->make_term(Not, fi)));
      clauses.push_back(
          s->make_term(Or,
                       s->make_term(Or, s->make_term(Not, le), ri),
                       s->make_term(Not, fi)));
    }
    else
    {  //((~a) v (~c)) and ((a) v (c))
      Term le = (*(se->begin()));
      clauses.push_back(
          s->make_term(Or, s->make_term(Not, le), s->make_term(Not, fi)));
      clauses.push_back(s->make_term(Or, le, fi));
    }
  }
  // taking the and of all clauses generated to create the cnf
  Term ret = s->make_term(And, clauses);
  ret = s->make_term(And, parent, ret);

  return ret;
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
