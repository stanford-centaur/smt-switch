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
#include <iterator>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "smt-switch/datatype.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/sort.h"
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
  explicit OpsVisitor(std::unordered_set<Op> & out) : out_(out) {}

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
  std::unordered_set<Op> & out_;
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

void get_ops(const Term & term, std::unordered_set<Op> & out)
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
  if (op.check_sortedness(terms))
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
