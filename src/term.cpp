/*********************                                                        */
/*! \file term.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Clark Barrett
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Abstract interface for SMT terms.
**
**
**/

#include "term.h"

#include <cstdint>
#include <memory>
#include <string>

#include "exceptions.h"
#include "sort.h"
#include "utils.h"

namespace smt {

std::wstring AbsTerm::getStringValue() const
{
  throw NotImplementedException("Strings not supported for this solver.");
}

std::int64_t AbsTerm::to_signed_int() const
{
  // to_string is not const only because a backend may cache the string
  const std::string repr = const_cast<AbsTerm *>(this)->to_string();
  if (!is_value())
  {
    throw IncorrectUsageException("Can't convert non-value " + repr
                                  + " to an integer");
  }
  SortKind sk = get_sort()->get_sort_kind();
  if (sk == BV)
  {
    return smtlib_bv_to_int64(repr);
  }
  if (sk == INT || sk == REAL)
  {
    return smtlib_int_to_int64(repr);
  }
  throw IncorrectUsageException("Can't convert " + repr
                                + " to an integer: it has sort "
                                + get_sort()->to_string());
}

std::ostream & operator<<(std::ostream & output, const Term t)
{
  output << t->to_string();
  return output;
}

/* TermIterBase implementation */
const Term TermIterBase::operator*()
{
  std::shared_ptr<AbsTerm> s;
  return s;
}

bool TermIterBase::operator==(const TermIterBase & other) const
{
  return (typeid(*this) == typeid(other)) && equal(other);
}
/* end TermIterBase implementation */

/* TermIter implementation */
TermIter & TermIter::operator=(const TermIter & other)
{
  // clone before deleting: on self-assignment, other.iter_ is iter_
  TermIterBase * copy = other.iter_ ? other.iter_->clone() : nullptr;
  delete iter_;
  iter_ = copy;
  return *this;
}

TermIter & TermIter::operator=(TermIter && other) noexcept
{
  if (this != &other)
  {
    delete iter_;
    iter_ = other.iter_;
    other.iter_ = nullptr;
  }
  return *this;
}

TermIter & TermIter::operator++()
{
  ++(*iter_);
  return *this;
}

TermIter TermIter::operator++(int)
{
  TermIter it = *this;
  ++(*iter_);
  return it;
}

bool TermIter::operator==(const TermIter & other) const
{
  if (iter_ == other.iter_)
  {
    return true;
  }
  // a default-constructed iterator equals only another one
  if (!iter_ || !other.iter_)
  {
    return false;
  }
  return *iter_ == *other.iter_;
}

bool TermIter::operator!=(const TermIter & other) const
{
  return !(*this == other);
}
/* end TermIter implementation */
}  // namespace smt
