/*********************                                                        */
/*! \file logging_term.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Class that wraps another Term object and maintains the expected
**        Op and children (for solvers that rewrite terms on the fly).
**
**/

#include "logging_term.h"

#include "exceptions.h"
#include "utils.h"

using namespace std;

namespace smt {

/* LoggingTerm */

LoggingTerm::LoggingTerm(Term t, Sort s, Op o, TermVec c, size_t id)
    : wrapped_term(t),
      sort(s),
      op(o),
      children(c),
      is_sym(false),
      is_par(false),
      id_(id)
{
}

LoggingTerm::LoggingTerm(
    Term t, Sort s, Op o, TermVec c, string r, bool is_sym, size_t id)
    : wrapped_term(t),
      sort(s),
      op(o),
      children(c),
      repr(r),
      is_sym(is_sym),
      is_par(!is_sym),
      id_(id)
{
}

LoggingTerm::~LoggingTerm() {}

// implemented

size_t LoggingTerm::get_id() const { return id_; }

bool LoggingTerm::compare(const Term & t) const
{
  // This methods compares two LoggingTerms
  // it is a particularly tricky implementation compared to the
  // compare method in other implementations of AbsTerm
  // If the underlying terms are different, then this will return false
  // However, even if the underlying terms are the same, this might
  // still need to return false. It needs to check that the sort,
  // operator and children are the same to keep the contract that
  // the logging term hides sort aliasing and term rewriting
  // Furthermore, we want to avoid recursively calling compare
  // on the whole term DAG because the children are also LoggingTerms
  // which rely on this method for equality
  // Because we perform hash-consing, we can only compare the pointer values
  // to compare children. See the use of .get() on the children below.
  // However, we do not just compare the pointer value of this term with
  // the pointer value of the argument t.
  // This is because we actually need to use this compare method for equality
  // when looking up this term in the hash table to perform hash-consing.
  // which is done when constructing the term. At this point, it still has
  // a different pointer value.
  // Thus, we cannot count on the pointers of this term and the argument t
  // to be equal. Instead we want to check that they represent the same term.
  // which is true if the underlying terms are the same, and they both have
  // the same Op, Sort, and children.

  if (!t)
  {
    // not equivalent to null term
    return false;
  }

  my_ptr<LoggingTerm> lt = static_pointer_cast<LoggingTerm>(t);

  // compare wrapped term and the LoggingSort
  // this handles values (e.g. null operators and no children)
  // and because of the sort comparison also handles sort aliasing
  // of the wrapped solver
  if (wrapped_term != lt->wrapped_term || sort != lt->sort)
  {
    return false;
  }

  // compare op
  if (op != lt->op)
  {
    return false;
  }

  // finally need to make sure all children match
  // this is the most expensive check, so we do it last
  if (children.size() != lt->children.size())
  {
    return false;
  }
  else
  {
    for (size_t i = 0; i < children.size(); i++)
    {
      // because of hash-consing, we can compare the pointers
      // otherwise would recursively call compare on the LoggingTerm children
      // Note: calling get() intead of comparing the Term my_ptrs directly
      // because operator== is overloaded for Terms such that it uses the
      // compare method of the underlying object (i.e. it would be a recursive
      // call to compare)
      if (children[i].get() != lt->children[i].get())
      {
        return false;
      }
    }
  }
  return true;
}

Op LoggingTerm::get_op() const { return op; }

Sort LoggingTerm::get_sort() const { return sort; }

string LoggingTerm::to_string()
{
  if (!repr.empty())
  {
    return repr;
  }

  // rely on underlying term for values
  // this is because values are often produced by the underlying solver
  // e.g. from get_value
  // so we couldn't assign a string at the smt-switch level
  if (op.is_null() && is_value())
  {
    return wrapped_term->print_value_as(sort->get_sort_kind());
  }
  else
  {
    // Op should not be null because handled values above
    //     and symbols already have the repr set
    Assert(!op.is_null());
    repr = "(";
    repr += op.to_string();
    for (auto c : children)
    {
      repr += " " + c->to_string();
    }
    repr += ")";
    return repr;
  }
}

bool LoggingTerm::is_symbol() const
{
  // functions, parameters, and symbolic constants are all symbols
  return is_sym || is_par;
}

bool LoggingTerm::is_param() const { return op.is_null() && is_par; }

bool LoggingTerm::is_symbolic_const() const
{
  return is_sym && sort->get_sort_kind() != FUNCTION;
}

TermIter LoggingTerm::begin()
{
  return TermIter(new LoggingTermIter(children.begin()));
}

TermIter LoggingTerm::end()
{
  return TermIter(new LoggingTermIter(children.end()));
}

// dispatched to underlying term

size_t LoggingTerm::hash() const { return wrapped_term->hash(); }

// check if op is null because a non-value
// may have been simplified to a value by the underlying solver
bool LoggingTerm::is_value() const { return op.is_null() && wrapped_term->is_value(); }

uint64_t LoggingTerm::to_int() const { return wrapped_term->to_int(); }

std::string LoggingTerm::print_value_as(SortKind sk)
{
  return wrapped_term->print_value_as(sk);
}

/* LoggingTermIter */

LoggingTermIter::LoggingTermIter(TermVec::iterator i) : it(i) {}

LoggingTermIter::LoggingTermIter(const LoggingTermIter & lit) : it(lit.it) {}

LoggingTermIter::~LoggingTermIter() {}

LoggingTermIter & LoggingTermIter::operator=(const LoggingTermIter & lit)
{
  it = lit.it;
  return *this;
}

void LoggingTermIter::operator++() { it++; }

const Term LoggingTermIter::operator*() { return *it; }

TermIterBase * LoggingTermIter::clone() const
{
  return new LoggingTermIter(it);
}

bool LoggingTermIter::operator==(const LoggingTermIter & lit)
{
  return it == lit.it;
}

bool LoggingTermIter::operator!=(const LoggingTermIter & lit)
{
  return it != lit.it;
}

bool LoggingTermIter::equal(const TermIterBase & other) const
{
  const LoggingTermIter & lit = static_cast<const LoggingTermIter &>(other);
  return it == lit.it;
}

}  // namespace smt
