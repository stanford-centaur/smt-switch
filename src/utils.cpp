/*!
 * \file utils.cpp
 * \brief Utility functions
 * \author Ahmed Irfan
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/utils.h"

#include <memory>
#include <unordered_set>
#include <vector>

#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"
#include "smt-switch/term_visitor.h"

namespace smt {

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

}  // namespace smt
