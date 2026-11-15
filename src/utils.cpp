/*!
 * \file utils.cpp
 * \brief Utility functions
 * \author Ahmed Irfan
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/utils.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <iterator>
#include <map>
#include <random>
#include <sstream>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "smt-switch/datatype.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/identity_walker.h"
#include "smt-switch/ops.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/sort.h"
#include "smt-switch/sort_inference.h"
#include "smt-switch/term.h"
#include "smt-switch/term_visitor.h"

namespace smt {

namespace detail {

void throw_foreign_handle(const Term & h)
{
  throw IncorrectUsageException("Term " + h->to_string()
                                + " was made by another solver");
}

void throw_foreign_handle(const Sort & h)
{
  throw IncorrectUsageException("Sort " + h->to_string()
                                + " was made by another solver");
}

void throw_foreign_handle(const DatatypeDecl & h)
{
  throw IncorrectUsageException("Datatype declaration " + h->get_name()
                                + " was made by another solver");
}

void throw_foreign_handle(const DatatypeConstructorDecl & h)
{
  throw IncorrectUsageException("Datatype constructor declaration "
                                + h->get_name()
                                + " was made by another solver");
}

void throw_foreign_handle(const Datatype & h)
{
  throw IncorrectUsageException("Datatype " + h->get_name()
                                + " was made by another solver");
}

}  // namespace detail

namespace {

// Goes down through the applications of one operator and collects the
// terms where they stop
class OpPartitionVisitor : public TermVisitor
{
 public:
  OpPartitionVisitor(PrimOp op, TermVec & out) : op_(op), out_(out) {}

 protected:
  VisitResult visit_term(const Term & term) override
  {
    if (term->get_op().prim_op == op_)
    {
      return VisitResult::Continue;
    }
    out_.push_back(term);
    return VisitResult::Skip;
  }

 private:
  PrimOp op_;
  TermVec & out_;
};

// Collects the terms that match, without going below them
class MatchingTermsVisitor : public TermVisitor
{
 public:
  MatchingTermsVisitor(bool (*matches)(const Term & term),
                       UnorderedTermSet & out)
      : matches_(matches), out_(out)
  {
  }

 protected:
  VisitResult visit_term(const Term & term) override
  {
    if (matches_(term))
    {
      out_.insert(term);
      return VisitResult::Skip;
    }
    return VisitResult::Continue;
  }

 private:
  bool (*matches_)(const Term & term);
  UnorderedTermSet & out_;
};

// Collects the operators of the applications in a term
class OpsVisitor : public TermVisitor
{
 public:
  explicit OpsVisitor(UnorderedOpSet & out) : out_(out) {}

 protected:
  VisitResult visit_term(const Term & term) override
  {
    Op op = term->get_op();
    // a null operator is a leaf's
    if (op.is_null())
    {
      return VisitResult::Skip;
    }
    out_.insert(op);
    return VisitResult::Continue;
  }

 private:
  UnorderedOpSet & out_;
};

// Collects the applications of some operators, going below each one too
class TermsWithOpsVisitor : public TermVisitor
{
 public:
  TermsWithOpsVisitor(const std::unordered_set<PrimOp> & ops,
                      UnorderedTermSet & out)
      : ops_(ops), out_(out)
  {
  }

 protected:
  VisitResult visit_term(const Term & term) override
  {
    Op op = term->get_op();
    if (!op.is_null() && ops_.find(op.prim_op) != ops_.end())
    {
      out_.insert(term);
    }
    return VisitResult::Continue;
  }

 private:
  const std::unordered_set<PrimOp> & ops_;
  UnorderedTermSet & out_;
};

// Collects the theory atoms of a formula, going through its connectives.
// With split_ites, an application with if-then-else children is visited
// once for each choice of their branches, and their conditions too.
class TheoryAtomsVisitor : public TermVisitor
{
 public:
  TheoryAtomsVisitor(const SmtSolver & solver,
                     bool split_ites,
                     UnorderedTermSet & out)
      : solver_(solver),
        boolsort_(solver->make_sort(BOOL)),
        split_ites_(split_ites),
        out_(out)
  {
  }

 protected:
  VisitResult visit_term(const Term & term) override
  {
    if (term->get_sort() != boolsort_ || term->is_value())
    {
      return VisitResult::Skip;
    }
    if (split_ites_)
    {
      // each child's choices: both branches of an if-then-else, else itself
      std::vector<TermVec> choices;
      bool has_ite = false;
      for (const Term & c : term)
      {
        if (c->get_op() == Ite)
        {
          has_ite = true;
          TermVec ite(c->begin(), c->end());
          visit(ite[0]);
          choices.push_back({ ite[1], ite[2] });
        }
        else
        {
          choices.push_back({ c });
        }
      }
      if (has_ite)
      {
        // count through every combination of choices, the first fastest
        std::vector<std::size_t> picks(choices.size(), 0);
        std::size_t i = 0;
        while (i < picks.size())
        {
          TermVec children;
          for (std::size_t j = 0; j < choices.size(); ++j)
          {
            children.push_back(choices[j][picks[j]]);
          }
          visit(solver_->make_term(term->get_op(), children));
          for (i = 0; i < picks.size() && ++picks[i] == choices[i].size(); ++i)
          {
            picks[i] = 0;
          }
        }
        return VisitResult::Continue;
      }
    }
    if (is_theory_atom(term, boolsort_))
    {
      out_.insert(term);
      return VisitResult::Skip;
    }
    return VisitResult::Continue;
  }

 private:
  SmtSolver solver_;
  Sort boolsort_;
  bool split_ites_;
  UnorderedTermSet & out_;
};

// Collects the symbolic constants that fix the values of terms in the
// model, following only the child that decides a term's value when one
// does
class JustificationVisitor : public TermVisitor
{
 public:
  JustificationVisitor(const SmtSolver & solver, UnorderedTermSet & out)
      : solver_(solver), out_(out)
  {
  }

 protected:
  VisitResult visit_term(const Term & term) override
  {
    Op op = term->get_op();
    if (op.is_null())
    {
      if (term->is_symbolic_const())
      {
        out_.insert(term);
      }
      return VisitResult::Skip;
    }
    TermVec children(term->begin(), term->end());
    if (op == Ite)
    {
      visit(children[0]);
      visit(solver_->get_value(children[0])->to_bool() ? children[1]
                                                       : children[2]);
      return VisitResult::Skip;
    }
    Term decider;
    if (op == And || op == Or)
    {
      // a false conjunct or a true disjunct
      bool deciding_value = op == Or;
      for (const Term & c : children)
      {
        if (solver_->get_value(c)->to_bool() == deciding_value)
        {
          decider = c;
          break;
        }
      }
    }
    else if (op == Implies)
    {
      // a false premise, else a true conclusion
      for (std::size_t i = 0; i + 1 < children.size() && !decider; ++i)
      {
        if (!solver_->get_value(children[i])->to_bool())
        {
          decider = children[i];
        }
      }
      if (!decider && solver_->get_value(children.back())->to_bool())
      {
        decider = children.back();
      }
    }
    else if (op == BVAnd || op == BVNand || op == BVMul)
    {
      for (const Term & c : children)
      {
        if (solver_->get_value(c)->to_bits().find('1') == std::string::npos)
        {
          decider = c;
          break;
        }
      }
    }
    else if (op == BVOr || op == BVNor)
    {
      for (const Term & c : children)
      {
        if (solver_->get_value(c)->to_bits().find('0') == std::string::npos)
        {
          decider = c;
          break;
        }
      }
    }
    if (decider)
    {
      visit(decider);
      return VisitResult::Skip;
    }
    return VisitResult::Continue;
  }

 private:
  SmtSolver solver_;
  UnorderedTermSet & out_;
};

}  // namespace

void op_partition(PrimOp o, const Term & term, TermVec & out)
{
  OpPartitionVisitor(o, out).visit(term);
}

void conjunctive_partition(const Term & term, TermVec & out, bool include_bvand)
{
  if (!include_bvand)
  {
    op_partition(And, term, out);
  }
  else
  {
    TermVec tmp;
    op_partition(And, term, tmp);
    Sort sort;
    for (auto tt : tmp)
    {
      sort = tt->get_sort();
      if (sort->get_sort_kind() == BV && sort->get_width() == 1)
      {
        op_partition(BVAnd, tt, out);
      }
      else
      {
        out.push_back(tt);
      }
    }
  }
}

void disjunctive_partition(const Term & term, TermVec & out, bool include_bvor)
{
  if (!include_bvor)
  {
    op_partition(Or, term, out);
  }
  else
  {
    TermVec tmp;
    op_partition(Or, term, tmp);
    Sort sort;
    for (auto tt : tmp)
    {
      sort = tt->get_sort();
      if (sort->get_sort_kind() == BV && sort->get_width() == 1)
      {
        op_partition(BVOr, tt, out);
      }
      else
      {
        out.push_back(tt);
      }
    }
  }
}

void get_matching_terms(const Term & term,
                        UnorderedTermSet & out,
                        bool (*matching_fun)(const Term & term))
{
  MatchingTermsVisitor(matching_fun, out).visit(term);
}

void get_free_symbolic_consts(const Term & term, UnorderedTermSet & out)
{
  auto f = [](const Term & t) { return t->is_symbolic_const(); };
  get_matching_terms(term, out, f);
}

void get_free_symbols(const Term & term, UnorderedTermSet & out)
{
  auto f = [](const Term & t) { return t->is_symbol(); };
  get_matching_terms(term, out, f);
}

void get_ops(const Term & term, UnorderedOpSet & out)
{
  OpsVisitor(out).visit(term);
}

void get_terms_with_ops(const Term & term,
                        const std::unordered_set<PrimOp> & ops,
                        UnorderedTermSet & out)
{
  TermsWithOpsVisitor(ops, out).visit(term);
}

void get_theory_atoms(const SmtSolver & solver,
                      const Term & formula,
                      UnorderedTermSet & out,
                      bool split_ites)
{
  TheoryAtomsVisitor(solver, split_ites, out).visit(formula);
}

void get_justifying_symbols(const SmtSolver & solver,
                            const Term & term,
                            UnorderedTermSet & out)
{
  JustificationVisitor(solver, out).visit(term);
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

bool is_theory_atom(const Term & t, const Sort & boolsort)
{
  // take a boolsort as an argument for sort aliasing solvers
  if (t->get_sort() != boolsort)
  {
    return false;
  }
  Op op = t->get_op();
  if (op.is_null())
  {
    return false;
  }
  PrimOp po = op.prim_op;
  if (po == And || po == Or || po == Xor || po == Not || po == Implies
      || po == Ite || po == Forall || po == Exists
      || po == Extract
      // the connectives of a solver that aliases Booleans and bit-vectors
      // of width one
      || po == BVAnd || po == BVOr || po == BVXor || po == BVNand || po == BVNor
      || po == BVXnor || po == BVNot)
  {
    return false;
  }
  // an equality or distinct over Booleans is a connective too
  return !((po == Equal || po == Distinct)
           && (*t->begin())->get_sort() == boolsort);
}

void cnf_to_dimacs(const Term & cnf, std::ostringstream & y)
{
  Sort sort = cnf->get_sort();
  if (sort->get_sort_kind() != BOOL)
  {
    throw IncorrectUsageException("cnf_to_dimacs expects a Boolean term, but "
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
      throw IncorrectUsageException("cnf_to_dimacs: " + cnf->to_string()
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
      else if (is_lit(t, sort) || (t->is_value() && !t->to_bool()))
      {
        after_or_elimination.push_back(t);
      }
      else
      {
        throw IncorrectUsageException("cnf_to_dimacs: " + cnf->to_string()
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

// The connective to_cnf encodes that t applies, or NUM_OPS_AND_NULL when t is
// a symbol, a constant or an atom that to_cnf keeps whole. Solvers that alias
// Bool with (_ BitVec 1) report bit-vector ops for the connectives.
PrimOp cnf_connective(const Term & t, const Sort & boolsort)
{
  if (t->get_sort() != boolsort)
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
  if (op == Equal && (*t->begin())->get_sort() == boolsort)
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
    PrimOp connective = cnf_connective(term, boolsort_);
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

    // to_cnf's clauses for xor read two children, but xor takes any number,
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
        boolsort_(solver->make_sort(BOOL)),
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
    PrimOp op = cnf_connective(term, boolsort_);
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
  Sort boolsort_;
  Term true_term_;
  Term false_term_;
};

}  // namespace

// returns true if the formula is in cnf form else false
bool is_cnf(Term formula)
{
  // similar as cnf_to_dimacs
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

Term to_cnf(Term formula, SmtSolver s)
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

// boolean ops and the bit-vector ops that mean the same, looked up from
// either side to swap one for the other
constexpr std::pair<PrimOp, PrimOp> bool_bv_ops[] = { { And, BVAnd },
                                                      { Or, BVOr },
                                                      { Xor, BVXor },
                                                      { Not, BVNot },
                                                      { Equal, BVComp } };

namespace {

/* A value term as another sort */
Term cast_value(const SmtSolver & solver, const Term & term, const Sort & sort)
{
  SortKind sk = sort->get_sort_kind();
  Sort cur_sort = term->get_sort();
  SortKind cur_sk = cur_sort->get_sort_kind();

  if (sk == BOOL && cur_sk == BV)
  {
    if (term->is_value() && cur_sort->get_width() == 1)
    {
      return solver->make_term(term->to_int() == 1);
    }
    throw NotImplementedException("Cannot interpret " + term->to_string()
                                  + " as a bool.");
  }
  else if (sk == BV && cur_sk == BOOL)
  {
    if (sort->get_width() != 1)
    {
      throw NotImplementedException("Cannot interpret " + term->to_string()
                                    + " as " + sort->to_string());
    }

    if (term->is_value())
    {
      return solver->make_term(term->to_bool() ? 1 : 0, sort);
    }
    throw NotImplementedException("Cannot interpret " + term->to_string()
                                  + " as " + sort->to_string());
  }
  else if (sk == REAL && cur_sk == INT)
  {
    return solver->make_term(To_Real, term);
  }
  else if (sk == ARRAY)
  {
    // this is a constant array
    // the only value that has SortKind ARRAY
    // make constant array by recursing on the element value
    return solver->make_term(
        cast_value(solver, *(term->begin()), sort->get_elemsort()), sort);
  }
  else
  {
    throw NotImplementedException("Interpreting " + term->to_string() + " as "
                                  + sort->to_string()
                                  + " is not yet implemented.");
  }
}

}  // namespace

Term cast_term(const SmtSolver & solver, const Term & term, const Sort & sort)
{
  Sort cur_sort = term->get_sort();
  if (cur_sort == sort)
  {
    // nothing to do
    return term;
  }
  else if (term->is_value())
  {
    return cast_value(solver, term, sort);
  }

  SortKind sk = sort->get_sort_kind();
  SortKind cur_sk = cur_sort->get_sort_kind();

  if (sk == BV && cur_sk == BOOL)
  {
    return solver->make_term(
        Ite, term, solver->make_term(1, sort), solver->make_term(0, sort));
  }
  else if (sk == BOOL && cur_sk == BV)
  {
    return solver->make_term(Equal, term, solver->make_term(1, cur_sort));
  }
  else if (sk == INT && cur_sk == REAL)
  {
    return solver->make_term(To_Int, term);
  }
  else if (sk == REAL && cur_sk == INT)
  {
    return solver->make_term(To_Real, term);
  }
  else
  {
    throw NotImplementedException("Cannot interpret " + term->to_string()
                                  + " as " + sort->to_string());
  }
}

Term cast_op(const SmtSolver & solver, const Op & op, const TermVec & terms)
{
  if (check_sortedness(op, terms))
  {
    return solver->make_term(op, terms);
  }

  PrimOp po = op.prim_op;

  // priority is turning bitvector operations to boolean operations
  // Heuristic, because boolector represents everything with bit-vector
  // operators, the most common scenario is turning bitvector ops to
  // boolean

  const auto * bool_bv_begin = std::begin(bool_bv_ops);
  const auto * bool_bv_end = std::end(bool_bv_ops);
  auto bool_is_po = [po](const auto & ops) { return ops.first == po; };
  auto bv_is_po = [po](const auto & ops) { return ops.second == po; };
  const auto * as_bool = std::find_if(bool_bv_begin, bool_bv_end, bv_is_po);
  const auto * as_bv = std::find_if(bool_bv_begin, bool_bv_end, bool_is_po);

  // case 1 -- bitvector to boolean op
  if (as_bool != bool_bv_end)
  {
    TermVec casted_children;
    casted_children.reserve(terms.size());
    Sort boolsort = solver->make_sort(BOOL);
    for (auto t : terms)
    {
      casted_children.push_back(cast_term(solver, t, boolsort));
    }
    return solver->make_term(as_bool->first, casted_children);
  }
  // case 2 -- boolean to bitvector op
  else if (as_bv != bool_bv_end)
  {
    TermVec casted_children;
    casted_children.reserve(terms.size());
    Sort bv1sort = solver->make_sort(BV, 1);
    for (auto t : terms)
    {
      casted_children.push_back(cast_term(solver, t, bv1sort));
    }
    return solver->make_term(as_bv->second, casted_children);
  }
  // case 3 -- cast all bit-vectors to booleans
  // a boolean operator that can't be converted to a bit-vector operator easily
  // (easily meaning by just switching the PrimOp)
  else if (po == Implies)
  {
    TermVec casted_children;
    casted_children.reserve(terms.size());
    Sort boolsort = solver->make_sort(BOOL);
    for (auto t : terms)
    {
      casted_children.push_back(cast_term(solver, t, boolsort));
    }
    return solver->make_term(po, casted_children);
  }
  // case 4 -- cast all booleans to bitvectors
  else if (get_theory(po) == Theory::BITVECTORS)
  {
    TermVec casted_children;
    casted_children.reserve(terms.size());
    Sort bv1sort = solver->make_sort(BV, 1);
    for (auto t : terms)
    {
      if (t->get_sort()->get_sort_kind() == BOOL)
      {
        casted_children.push_back(cast_term(solver, t, bv1sort));
      }
      else
      {
        // expecting a bit-vector
        casted_children.push_back(t);
      }
    }
    return solver->make_term(op, casted_children);
  }
  // case 5 -- special case for Ite
  else if (po == Ite)
  {
    Sort boolsort = solver->make_sort(BOOL);
    Term cond = cast_term(solver, terms[0], boolsort);

    Term ifbranch = terms[1];
    Term elsebranch = terms[2];

    SortKind ifsk = ifbranch->get_sort()->get_sort_kind();
    SortKind elsesk = elsebranch->get_sort()->get_sort_kind();
    if (ifsk == INT && elsesk == REAL)
    {
      // MathSAT and Yices2 make an integer-valued Real an Int, so an Ite
      // over Reals can have one branch of each; widen rather than truncate
      ifbranch = cast_term(solver, ifbranch, elsebranch->get_sort());
    }
    else if (ifbranch->get_sort() != elsebranch->get_sort())
    {
      // arbitrarily deciding to cast to the ifbranch sort
      elsebranch = cast_term(solver, elsebranch, ifbranch->get_sort());
    }

    return solver->make_term(Ite, cond, ifbranch, elsebranch);
  }
  // case 7 -- special case for ARRAY select
  else if (po == Select)
  {
    // assuming the array itself doesn't need to be casted
    // only the index
    // we have no support for or issue with that
    return solver->make_term(
        Select,
        terms[0],
        cast_term(solver, terms[1], terms[0]->get_sort()->get_indexsort()));
  }
  // case 8 -- special case for ARRAY store
  else if (po == Store)
  {
    // assuming the array itself doesn't need to be casted
    // only the index
    // we have no support for or issue with that
    Sort arrsort = terms[0]->get_sort();
    return solver->make_term(
        Store,
        terms[0],
        cast_term(solver, terms[1], arrsort->get_indexsort()),
        cast_term(solver, terms[2], arrsort->get_elemsort()));
  }
  // case 9 -- special case for FUNCTION
  else if (po == Apply)
  {
    Sort funsort = terms[0]->get_sort();
    // assuming the function itself does not need to be cast
    TermVec casted_children;
    casted_children.reserve(terms.size());
    casted_children.push_back(terms[0]);
    SortVec domain_sorts = funsort->get_domain_sorts();
    if (terms.size() != domain_sorts.size() + 1)
    {
      throw IncorrectUsageException("Can't apply " + terms[0]->to_string()
                                    + " of sort " + funsort->to_string()
                                    + " to " + std::to_string(terms.size() - 1)
                                    + " arguments");
    }
    for (size_t i = 1; i < terms.size(); ++i)
    {
      casted_children.push_back(
          cast_term(solver, terms[i], domain_sorts[i - 1]));
    }
    return solver->make_term(Apply, casted_children);
  }
  // case 10 -- a quantifier, whose body is a bit-vector of width one in a
  // solver that aliases the two
  else if (po == Forall || po == Exists)
  {
    TermVec casted_children(terms.begin(), terms.end() - 1);
    casted_children.push_back(
        cast_term(solver, terms.back(), solver->make_sort(BOOL)));
    return solver->make_term(op, casted_children);
  }
  // default case
  else
  {
    std::string msg("Cannot cast this operation: (");
    msg += op.to_string();
    for (auto t : terms)
    {
      msg += " " + t->to_string();
    }
    msg += ")";
    throw NotImplementedException(msg);
  }
}

// ----------------------------------------------------------------------------

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
    reducer_->assert_formula(reducer_->make_term(Implies, l, a));
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
    reducer_->assert_formula(reducer_->make_term(Implies, l, a));
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
          reducer_->make_sort(BOOL));
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

// ----------------------------------------------------------------------------

DisjointSet::DisjointSet(bool (*c)(const Term & a, const Term & b)) : comp(c) {}

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
      leader_[a] = b;
      leader_[b] = b;
      group_[b] = UnorderedTermSet({ a, b });
    }
  }
}

Term DisjointSet::find(const Term & t) const
{
  auto it = leader_.find(t);
  if (it == leader_.end())
  {
    throw IncorrectUsageException("DisjointSet::find: " + t->to_string()
                                  + " was never added");
  }
  return it->second;
}

void DisjointSet::clear()
{
  leader_.clear();
  group_.clear();
}

// -----------------------------------------------------------------------------

std::string internal_name(const std::string & kind, std::uint64_t index)
{
  return std::string(INTERNAL_NAME_PREFIX) + kind + "_" + std::to_string(index);
}

bool is_internal_name(std::string_view name)
{
  return name.compare(0, INTERNAL_NAME_PREFIX.size(), INTERNAL_NAME_PREFIX)
         == 0;
}

}  // namespace smt
