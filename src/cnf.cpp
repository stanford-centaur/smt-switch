/*!
 * \file cnf.cpp
 * \brief Conversion of Boolean formulas to CNF and DIMACS
 * \author Bhaskar Gupta
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/cnf.h"

#include <cstddef>
#include <map>
#include <memory>
#include <string>
#include <vector>

#include "smt-switch/exceptions.h"
#include "smt-switch/identity_walker.h"
#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

namespace smt::cnf {

void to_dimacs(const Term & cnf, std::ostringstream & y)
{
  Sort sort = cnf->get_sort();
  if (!sort->is_boolean())
  {
    throw IncorrectUsageException("cnf::to_dimacs expects a Boolean term, but "
                                  + cnf->to_string() + " has sort "
                                  + sort->to_string());
  }
  if (cnf->is_value() && cnf->to_bool())
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
    Op op = t->get_op();
    if (!(op.is_null() || op == Or || op == And || op == Not))
    {
      throw IncorrectUsageException("cnf::to_dimacs: " + cnf->to_string()
                                    + " is not in CNF");
    }
    if (op.prim_op == And)
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
      if (t->get_op() == Or)
      {
        for (auto child : t)
        {
          before_or_elimination.push_back(child);
        }
      }
      else if (t->is_lit() || (t->is_value() && !t->to_bool()))
      {
        after_or_elimination.push_back(t);
      }
      else
      {
        throw IncorrectUsageException("cnf::to_dimacs: " + cnf->to_string()
                                      + " is not in CNF");
      }
    }
    clauses.push_back(after_or_elimination);
  }

  std::map<Term, int> ma;  // This map will create a mapping from symbols to
                           // distinct contiguous integer values.
  int ptr = 0;             // pointer to store the next integer used in mapping

  // iterating within each clause and mapping every distinct symbol to a
  // natural number
  for (auto u : clauses)
  {
    for (auto uu : u)
    {  // Using literals from all the clauses to create the mapping
      if (uu->is_value())
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
  // printing the output in DIMACS format
  y << "p cnf ";
  y << ptr;  // number of distinct symbols
  y << " ";

  size_t sz = clauses.size();

  y << sz;  // number of clauses
  y << "\n";

  // iterating within each clause and assigning the literal their mapped
  // value(for a positive literal) or it's negative value(for a negative
  // literal)
  for (auto u : clauses)
  {
    for (auto uu : u)
    {
      if (uu->is_value())
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

namespace {

// The connective convert encodes that t applies, or NUM_OPS_AND_NULL when t is
// a symbol, a constant or an atom that convert keeps whole. Solvers that alias
// Bool with (_ BitVec 1) report bit-vector ops for the connectives.
PrimOp cnf_connective(const Term & t)
{
  if (!t->get_sort()->is_boolean())
  {
    return NUM_OPS_AND_NULL;
  }
  PrimOp op = t->get_op().prim_op;
  if (op == Not || op == BVNot)
  {
    return Not;
  }
  if (op == And || op == BVAnd)
  {
    return And;
  }
  if (op == Or || op == BVOr)
  {
    return Or;
  }
  if (op == Xor || op == BVXor)
  {
    return Xor;
  }
  if (op == Implies)
  {
    return Implies;
  }
  if (op == Equal && (*t->begin())->get_sort()->is_boolean())
  {
    return Equal;
  }
  return NUM_OPS_AND_NULL;
}

// Names each connective with a fresh symbol and records its definition,
// name <-> (connective children), where each child is the name of a
// connective or an atom
class TseitinTraversal : public IdentityWalker
{
 public:
  struct Definition
  {
    Term name;
    PrimOp connective;
    TermVec children;
  };
  std::vector<Definition> reduced = {};

  explicit TseitinTraversal(const SmtSolver & solver)
      : IdentityWalker{ solver, false }, boolsort_(solver->make_sort(BOOL))
  {
  }
  WalkerStepResult visit_term(Term & term) override
  {
    auto give_symbolic_name = [&]() {  // producing a new symbol
      int pt = 1;
      while (true)
      {
        try
        {
          return solver_->make_symbol("tseitin_to_cnf_" + std::to_string(pt),
                                      boolsort_);
        }
        catch (IncorrectUsageException & e)
        {
          pt++;
        }
      }

    };
    PrimOp connective = cnf_connective(term);
    if (connective == NUM_OPS_AND_NULL)
    {
      // a symbol or an atom stands for itself, and skipping it keeps the
      // connectives inside an atom from being named
      save_in_cache(term, term);
      return Walker_Skip;
    }
    if (preorder_)
    {
      // a connective is named after its children
      return Walker_Continue;
    }

    // every child is cached by now: an atom when it was first seen, a
    // connective when it was named
    TermVec children;
    for (auto u : term)
    {
      Term cached_term;
      query_cache(u, cached_term);
      children.push_back(cached_term);
    }

    // convert's clauses for xor read two children, but xor takes any number,
    // so name every step but the last, left associative. => and = need no
    // such step: EliminateBooleanConstants leaves them binary
    if (connective == Xor)
    {
      Term acc = children[0];
      for (size_t i = 1; i + 1 < children.size(); ++i)
      {
        Term step = give_symbolic_name();
        reduced.push_back({ step, Xor, { acc, children[i] } });
        acc = step;
      }
      children = { acc, children.back() };
    }

    Term term_name = give_symbolic_name();  // making a new symbol
    save_in_cache(term, term_name);

    reduced.push_back({ term_name, connective, children });
    return Walker_Continue;
  }

 private:
  Sort boolsort_;
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
  explicit EliminateBooleanConstants(const SmtSolver & solver)
      : IdentityWalker{ solver, false },
        true_term_(solver->make_term(true)),
        false_term_(solver->make_term(false))
  {
  }
  WalkerStepResult visit_term(Term & term) override
  {
    auto cached_children = [&]() {
      TermVec children;
      for (auto u : term)
      {
        Term cached_term;
        query_cache(u, cached_term);
        children.push_back(cached_term);
      }
      return children;
    };
    auto simplify_equal = [&](const Term & lhs_cached,
                              const Term & rhs_cached) -> Term {
      // (lhs<->rhs)
      if ((lhs_cached == true_term_ && rhs_cached == true_term_)
          || (lhs_cached == false_term_ && rhs_cached == false_term_))
      {  //(true==true)=true, (false==false)=true
        return true_term_;
      }
      else if ((lhs_cached == true_term_ && rhs_cached == false_term_)
               || (lhs_cached == false_term_ && rhs_cached == true_term_))
      {  //(true==false)=false, (false==true)=false
        return false_term_;
      }
      else if (lhs_cached == true_term_)
      {  //(true==rhs)=rhs
        return rhs_cached;
      }
      else if (rhs_cached == true_term_)
      {  //(lhs==true)=lhs
        return lhs_cached;
      }
      else if (lhs_cached == false_term_)
      {  //(false==rhs)=not(rhs)
        return solver_->make_term(Not, rhs_cached);
      }
      else if (rhs_cached == false_term_)
      {  //(lhs==false)=not(lhs)
        return solver_->make_term(Not, lhs_cached);
      }
      // keeping it as it is
      return solver_->make_term(Equal, lhs_cached, rhs_cached);
    };
    auto simplify_implies = [&](const Term & lhs_cached,
                                const Term & rhs_cached) -> Term {
      if (lhs_cached == false_term_ || rhs_cached == true_term_)
      {  //(false->?)=true, (?->true)=true
        return true_term_;
      }
      else if (lhs_cached == true_term_)
      {  //(true->rhs)=rhs
        return rhs_cached;
      }
      else if (rhs_cached == false_term_)
      {  //(lhs->false)=not(lhs)
        return solver_->make_term(Not, lhs_cached);
      }
      // keeping it as it is, as neither lhs or rhs is either "true" or
      // "false"
      return solver_->make_term(Implies, lhs_cached, rhs_cached);
    };
    auto simplify_and = [&](const TermVec & conjuncts) -> Term {
      std::vector<Term> vec;  // contains all children which are neither
                              // "true" nor "false"
      for (const Term & cached_term : conjuncts)
      {
        if (cached_term == false_term_)
        {  // if any child is false, the entire expression is false
          return false_term_;
        }
        if (cached_term != true_term_)
        {
          vec.push_back(cached_term);
        }
      }
      if (vec.empty())
      {  // if all children are true, the expression is true
        return true_term_;
      }
      else if (vec.size() == 1)
      {  // if just one child is neither true nor false, that child is
         // equivalent to the entire formula
        return vec[0];
      }
      // keeping it as it is
      return solver_->make_term(And, vec);
    };
    PrimOp op = cnf_connective(term);
    if (op == NUM_OPS_AND_NULL)
    {
      // symbols, constants and atoms are kept as they are, and their
      // subterms are not visited
      save_in_cache(term, term);
      return Walker_Skip;
    }
    if (!preorder_)
    {
      if (op == Not)
      {
        Term t = (*term->begin());
        Term cached_term;
        query_cache(t,
                    cached_term);  // Querying the mapped formula of the child
                                   // as we are doing a preorder traversal

        if (cached_term == true_term_)
        {  // not(false)=true
          save_in_cache(term, false_term_);
        }
        else if (cached_term == false_term_)
        {  // not(true)=false
          save_in_cache(term, true_term_);
        }
        else
        {  // mapping not of the queried term_name.
          save_in_cache(term, solver_->make_term(Not, cached_term));
        }
      }
      else if (op == Equal)
      {
        // chainable: the conjunction of each adjacent pair's equality
        TermVec children = cached_children();
        TermVec pairs;
        for (size_t i = 0; i + 1 < children.size(); ++i)
        {
          pairs.push_back(simplify_equal(children[i], children[i + 1]));
        }
        save_in_cache(term, simplify_and(pairs));
      }
      else if (op == Implies)
      {
        // right associative
        TermVec children = cached_children();
        Term acc = children.back();
        for (size_t i = children.size() - 1; i > 0; --i)
        {
          acc = simplify_implies(children[i - 1], acc);
        }
        save_in_cache(term, acc);
      }
      else if (op == And)
      {
        save_in_cache(term, simplify_and(cached_children()));
      }
      else if (op == Or)
      {
        std::vector<Term> vec;  // contains all children which are neither
                                // "true" nor "false"
        bool true_present = 0;  // true_present=1, if any child is "true"
        auto it = term->begin();
        while (it != term->end())
        {  // iterating over all children
          Term cached_term;
          query_cache((*it), cached_term);
          if (cached_term == true_term_)
          {
            true_present = 1;
            it++;
          }
          else if (cached_term == false_term_)
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
          save_in_cache(term, true_term_);
        }
        else if (vec.empty())
        {  // If all children are "false", the expression is "false"
          save_in_cache(term, false_term_);
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
      else if (op == Xor)
      {
        std::vector<Term> vec;  // contains all children which are neither
                                // "true" nor "false"
        int true_count = 0;
        auto it = term->begin();
        while (it != term->end())
        {  // iterating over all children
          Term cached_term;
          query_cache((*it), cached_term);
          if (cached_term == true_term_)
          {
            it++;
            true_count++;
          }
          else if (cached_term == false_term_)
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
          if (true_count % 2 == 0)
          {  // even number of "true" implies the expression is false
            save_in_cache(term, false_term_);
          }
          else
          {  // odd number of "true" implies the expression is false
            save_in_cache(term, true_term_);
          }
        }
        else if (vec.size() == 1)
        {
          if (true_count % 2 == 0)
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
          if (true_count % 2 == 0)
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

    return Walker_Continue;
  }
  Term acc_cache(Term term)
  {
    Term ne;
    query_cache(term, ne);
    return ne;
  }

 private:
  Term true_term_;
  Term false_term_;
};

}  // namespace

// returns true if the formula is in cnf form else false
bool is_cnf(Term formula)
{
  // similar as to_dimacs
  // first remove the ands in the outermost layer, then remove the ors from the
  // next level. The remaining terms should be literals
  if (formula->is_symbolic_const())
  {
    return true;
  }

  TermVec before_and_elimination({ formula });
  TermVec after_and_elimination;
  while (!before_and_elimination.empty())
  {
    Term t = before_and_elimination.back();
    before_and_elimination.pop_back();
    Op op = t->get_op();
    if (op.prim_op == And)
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
      Op op = t->get_op();
      if (op.prim_op == Or)
      {
        for (auto child : t)
        {
          before_or_elimination.push_back(child);
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
      Op op = literal->get_op();
      if (op == Not && (*(literal->begin()))->is_symbolic_const())
      {
        continue;
      }

      check = 0;  // if the term is not a literal
    }
  }
  return check;
}

Term convert(Term formula, SmtSolver s)
{
  EliminateBooleanConstants elim(s);
  elim.visit(formula);  // removing "true" and "false" present in formula
  formula = elim.acc_cache(formula);

  if (formula->is_symbolic_const())
  {
    return formula;
  }
  // with its constants eliminated, a formula is a value only if it is true
  // or false
  if (formula->is_value())
  {
    return formula;
  }

  if (is_cnf(formula))  // if the expression is already in cnf just return it
  {
    return formula;
  }

  TseitinTraversal obj(s);
  obj.visit(formula);  // traversing the formula to create the definitions
                       // (c<->(a op b)) used in the transformation

  if (obj.reduced.empty())
  {
    // the formula is a single atom
    return formula;
  }
  Term parent = obj.reduced.back().name;

  TermVec clauses;

  // each definition in reduced is (c)<->(a op b), where c is its name and
  // a, b are its children

  for (const auto & definition : obj.reduced)
  {
    const Term & name = definition.name;
    const TermVec & children = definition.children;
    PrimOp op = definition.connective;

    if (op == Or)
    {  //(c<->Or(x1, x2, x3, x4....)) = (Or(~c, x1, x2, x3, x4) And (And((c or
       //~x1), (c or ~x2), (c or ~x3), (c or ~x4))
      std::vector<Term> vec;
      std::vector<Term> vec2;
      vec.push_back(s->make_term(Not, name));
      for (auto u : children)
      {
        vec.push_back(u);
        vec2.push_back(s->make_term(Or, name, s->make_term(Not, u)));
      }
      clauses.push_back(s->make_term(Or, vec));
      clauses.push_back(s->make_term(And, vec2));
    }
    else if (op == And)
    {  //(c<->And(x1, x2, x3, x4....)) = (Or(c, ~x1, ~x2, ~x3, ~x4) And (And((~c
       // or x1), (~c or x2), (~c or x3), (~c or x4))
      std::vector<Term> vec;
      std::vector<Term> vec2;
      vec.push_back(name);
      for (auto u : children)
      {
        vec.push_back(s->make_term(Not, u));
        vec2.push_back(s->make_term(Or, u, s->make_term(Not, name)));
      }
      clauses.push_back(s->make_term(Or, vec));
      clauses.push_back(s->make_term(And, vec2));
    }
    else if (op == Xor)
    {  //((~a) v (~b) v (~c)) and ((a) v (b) v (~c)) and ((c) v (b) v (~a)) and
       //((c) v (a) v (~b))
      auto it = children.begin();
      Term lhs = (*it);
      it++;
      Term rhs = (*it);
      clauses.push_back(s->make_term(
          Or,
          s->make_term(Or, s->make_term(Not, lhs), s->make_term(Not, rhs)),
          s->make_term(Not, name)));
      clauses.push_back(s->make_term(
          Or, s->make_term(Or, lhs, rhs), s->make_term(Not, name)));
      clauses.push_back(s->make_term(
          Or, s->make_term(Or, name, rhs), s->make_term(Not, lhs)));
      clauses.push_back(s->make_term(
          Or, s->make_term(Or, name, lhs), s->make_term(Not, rhs)));
    }
    else if (op == Implies)
    {  //((~a) v (b) v (~c)) and ((a) v (c)) and ((~b) v (c))
      auto it = children.begin();
      Term lhs = (*it);
      it++;
      Term rhs = (*it);
      clauses.push_back(
          s->make_term(Or,
                       s->make_term(Or, s->make_term(Not, lhs), rhs),
                       s->make_term(Not, name)));
      clauses.push_back(s->make_term(Or, lhs, name));
      clauses.push_back(s->make_term(Or, s->make_term(Not, rhs), name));
    }
    else if (op == Equal)
    {  //((~a) v (~b) v (c)) and ((a) v (b) v (c)) and ((~c) v (~b) v (a)) and
       //((c) v (~a) v (b))
      auto it = children.begin();
      Term lhs = (*it);
      it++;
      Term rhs = (*it);
      clauses.push_back(s->make_term(
          Or,
          s->make_term(Or, s->make_term(Not, lhs), s->make_term(Not, rhs)),
          name));
      clauses.push_back(s->make_term(Or, s->make_term(Or, lhs, rhs), name));
      clauses.push_back(
          s->make_term(Or,
                       s->make_term(Or, lhs, s->make_term(Not, rhs)),
                       s->make_term(Not, name)));
      clauses.push_back(
          s->make_term(Or,
                       s->make_term(Or, s->make_term(Not, lhs), rhs),
                       s->make_term(Not, name)));
    }
    else
    {  // Not, the only connective left: ((~a) v (~c)) and ((a) v (c))
      Term lhs = children[0];
      clauses.push_back(
          s->make_term(Or, s->make_term(Not, lhs), s->make_term(Not, name)));
      clauses.push_back(s->make_term(Or, lhs, name));
    }
  }
  // taking the and of all clauses generated to create the cnf
  Term ret = s->make_term(And, clauses);
  ret = s->make_term(And, parent, ret);

  return ret;
}

}  // namespace smt::cnf
