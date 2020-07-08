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

LoggingTerm::LoggingTerm(Term t, Sort s, Op o, TermVec c)
    : wrapped_term(t), sort(s), op(o), children(c), is_sym(false), is_par(false)
{
}

LoggingTerm::LoggingTerm(Term t, Sort s, Op o, TermVec c, string r, bool is_sym)
    : wrapped_term(t),
      sort(s),
      op(o),
      children(c),
      repr(r),
      is_sym(is_sym),
      is_par(!is_sym)
{
}

LoggingTerm::~LoggingTerm() {}

// implemented
bool LoggingTerm::compare(const Term & t) const
{
  if (!t)
  {
    // not equivalent to null term
    return false;
  }

  shared_ptr<LoggingTerm> lt = static_pointer_cast<LoggingTerm>(t);

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

bool LoggingTerm::is_param() const { return is_par; }

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

bool LoggingTerm::is_value() const { return wrapped_term->is_value(); }

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
