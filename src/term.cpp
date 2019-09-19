#include "term.h"

namespace smt {

bool operator==(const Term & t1, const Term & t2) { return t1->compare(t2); }

bool operator!=(const Term & t1, const Term & t2) { return !t1->compare(t2); }

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
  delete iter_;
  iter_ = other.iter_->clone();
  return *this;
}

TermIter & TermIter::operator++()
{
  ++(*iter_);
  return *this;
}

bool TermIter::operator==(const TermIter & other) const
{
  return (iter_ == other.iter_) || (*iter_ == *other.iter_);
}

bool TermIter::operator!=(const TermIter & other) const
{
  return !(*this == other);
}
/* end TermIter implementation */
}  // namespace smt
