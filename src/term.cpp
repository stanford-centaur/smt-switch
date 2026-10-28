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

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <typeinfo>

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
  const std::string repr = to_string();
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

/* TermIterBase implementation */
TermIterBase::~TermIterBase() = default;

bool TermIterBase::operator==(const TermIterBase & other) const
{
  return (typeid(*this) == typeid(other)) && equal(other);
}

bool TermIterBase::operator!=(const TermIterBase & other) const
{
  return !(*this == other);
}
/* end TermIterBase implementation */

/* TermIter implementation */
TermIter::TermIter(TermIterBase * tib) : iter_(tib) {}

// a default-constructed iterator holds no iter_, so copy it as null
TermIter::TermIter(const TermIter & other)
    : iter_(other.iter_ ? other.iter_->clone() : nullptr)
{
}

TermIter & TermIter::operator=(const TermIter & other)
{
  // clone before resetting: on self-assignment, other.iter_ is iter_
  iter_.reset(other.iter_ ? other.iter_->clone() : nullptr);
  return *this;
}

TermIter & TermIter::operator++()
{
  if (!iter_)
  {
    throw IncorrectUsageException("Cannot increment a null term iterator");
  }
  ++(*iter_);
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
  if (!iter_)
  {
    throw IncorrectUsageException("Cannot dereference a null term iterator");
  }
  return *(*iter_);
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

}  // namespace smt

namespace std {

size_t hash<smt::Term>::operator()(const smt::Term & t) const
{
  return t ? t->hash() : 0;
}

}  // namespace std
