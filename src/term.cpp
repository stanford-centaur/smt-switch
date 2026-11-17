/*!
 * \file term.cpp
 * \brief Abstract interface for SMT terms
 * \author Makai Mann
 * \author Clark Barrett
 * \author Áron Ricardo Perez-Lopez
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/term.h"

#include <cstddef>
#include <cstdint>
#include <memory>
#include <ostream>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

#include "smt-switch/exceptions.h"
#include "smt-switch/numeral_utils.h"
#include "smt-switch/sort.h"
#include "smt-switch/term_visitor.h"
#include "smt-switch/visit_result.h"

namespace smt {

std::wstring AbsTerm::getStringValue() const
{
  throw NotImplementedException("Strings not supported for this solver.");
}

std::int64_t AbsTerm::to_signed_int() const
{
  const std::string repr = to_string();
  if (!is_value())
  {
    throw IncorrectUsageException("Can't convert non-value " + repr
                                  + " to an integer");
  }
  SortKind sk = get_sort()->get_kind();
  if (sk == SortKind::BV)
  {
    return bits_to_int64(to_bits());
  }
  if (sk == SortKind::INT || sk == SortKind::REAL)
  {
    return smtlib::int_to_int64(repr);
  }
  throw IncorrectUsageException("Can't convert " + repr
                                + " to an integer: it has sort "
                                + get_sort()->to_string());
}

std::string AbsTerm::to_bits() const
{
  const std::string repr = to_string();
  if (!is_value() || get_sort()->get_kind() != SortKind::BV)
  {
    throw IncorrectUsageException("Can't convert " + repr
                                  + " to bits: it is not a bit-vector value");
  }
  return smtlib::bv_to_bits(repr);
}

bool AbsTerm::to_bool() const
{
  const std::string repr = to_string();
  if (is_value() && get_sort()->get_kind() == SortKind::BOOL)
  {
    if (repr == "true")
    {
      return true;
    }
    if (repr == "false")
    {
      return false;
    }
  }
  throw IncorrectUsageException("Can't convert " + repr
                                + " to a Boolean: it is not a Boolean value");
}

bool operator==(const Term & t1, const Term & t2)
{
  if (!t1 || !t2)
  {
    return !t1 && !t2;
  }
  return t1->compare(t2);
}
bool operator!=(const Term & t1, const Term & t2) { return !(t1 == t2); }
bool operator<(const Term & t1, const Term & t2)
{
  if (!t1 || !t2)
  {
    return !t1 && t2;
  }
  return t1->get_id() < t2->get_id();
}
bool operator>(const Term & t1, const Term & t2) { return t2 < t1; }
bool operator<=(const Term & t1, const Term & t2) { return !(t2 < t1); }
bool operator>=(const Term & t1, const Term & t2) { return !(t1 < t2); }

std::ostream & operator<<(std::ostream & output, const Term t)
{
  output << (t ? t->to_string() : "null");
  return output;
}

TermIter AbsTerm::begin() const
{
  return TermIter(shared_from_this(), 0, get_num_children());
}

TermIter AbsTerm::end() const
{
  const std::size_t size = get_num_children();
  return TermIter(shared_from_this(), size, size);
}

/* TermIter implementation */
TermIter::TermIter(std::shared_ptr<const AbsTerm> t,
                   std::size_t p,
                   std::size_t s)
    : term(std::move(t)), position(p), size(s)
{
}

TermIter & TermIter::operator++()
{
  if (!term)
  {
    throw IncorrectUsageException("Cannot increment a null term iterator");
  }
  ++position;
  return *this;
}

TermIter TermIter::operator++(int)
{
  TermIter it = *this;
  ++(*this);
  return it;
}

Term TermIter::operator*() const
{
  if (!term)
  {
    throw IncorrectUsageException("Cannot dereference a null term iterator");
  }
  if (position >= size)
  {
    throw IncorrectUsageException("Cannot dereference past a term's children");
  }
  return term->get_child(position);
}

bool TermIter::operator==(const TermIter & other) const
{
  // compares the objects, not the terms they stand for
  return term.get() == other.term.get() && position == other.position;
}

bool TermIter::operator!=(const TermIter & other) const
{
  return !(*this == other);
}
/* end TermIter implementation */

TermIter begin(const Term & t)
{
  if (!t)
  {
    throw IncorrectUsageException("Cannot iterate over a null term");
  }
  return t->begin();
}

TermIter end(const Term & t)
{
  if (!t)
  {
    throw IncorrectUsageException("Cannot iterate over a null term");
  }
  return t->end();
}

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

void AbsTerm::op_partition(PrimOp o, TermVec & out)
{
  OpPartitionVisitor(o, out).visit(shared_from_this());
}

void AbsTerm::conjunctive_partition(TermVec & out, bool include_bvand)
{
  if (!include_bvand)
  {
    op_partition(And, out);
  }
  else
  {
    TermVec tmp;
    op_partition(And, tmp);
    Sort sort;
    for (auto tt : tmp)
    {
      sort = tt->get_sort();
      if (sort->get_kind() == SortKind::BV && sort->get_width() == 1)
      {
        tt->op_partition(BVAnd, out);
      }
      else
      {
        out.push_back(tt);
      }
    }
  }
}

void AbsTerm::disjunctive_partition(TermVec & out, bool include_bvor)
{
  if (!include_bvor)
  {
    op_partition(Or, out);
  }
  else
  {
    TermVec tmp;
    op_partition(Or, tmp);
    Sort sort;
    for (auto tt : tmp)
    {
      sort = tt->get_sort();
      if (sort->get_kind() == SortKind::BV && sort->get_width() == 1)
      {
        tt->op_partition(BVOr, out);
      }
      else
      {
        out.push_back(tt);
      }
    }
  }
}

void AbsTerm::get_matching_terms(UnorderedTermSet & out,
                                 bool (*matching_fun)(const Term & term))
{
  MatchingTermsVisitor(matching_fun, out).visit(shared_from_this());
}

void AbsTerm::get_free_symbolic_consts(UnorderedTermSet & out)
{
  auto f = [](const Term & t) { return t->is_symbolic_const(); };
  get_matching_terms(out, f);
}

void AbsTerm::get_free_symbols(UnorderedTermSet & out)
{
  auto f = [](const Term & t) { return t->is_symbol(); };
  get_matching_terms(out, f);
}

void AbsTerm::get_ops(std::unordered_set<Op> & out)
{
  OpsVisitor(out).visit(shared_from_this());
}

void AbsTerm::get_terms_with_ops(const std::unordered_set<PrimOp> & ops,
                                 UnorderedTermSet & out)
{
  TermsWithOpsVisitor(ops, out).visit(shared_from_this());
}

bool AbsTerm::is_lit()
{
  if (!get_sort()->is_boolean())
  {
    return false;
  }

  if (is_symbolic_const())
  {
    return true;
  }

  Op op = get_op();
  // check both for sort aliasing solvers
  if (op == Not || op == BVNot)
  {
    Term first_child = *(begin());
    return first_child->is_symbolic_const();
  }

  return false;
}

bool AbsTerm::is_theory_atom()
{
  if (!get_sort()->is_boolean())
  {
    return false;
  }
  Op op = get_op();
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
           && (*begin())->get_sort()->is_boolean());
}

}  // namespace smt

namespace std {

size_t hash<smt::Term>::operator()(const smt::Term & t) const
{
  return t ? t->hash() : 0;
}

}  // namespace std
