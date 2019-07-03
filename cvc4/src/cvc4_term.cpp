#include "api/cvc4cpp.h"

#include "exceptions.h"

#include "cvc4_sort.h"
#include "cvc4_term.h"

namespace smt {

// struct for hashing
CVC4::api::TermHashFunction termhash;

/* CVC4TermIter implementation */
CVC4TermIter & CVC4TermIter::operator=(const CVC4TermIter & it)
{
  term_it = it.term_it;
  return *this;
}

void CVC4TermIter::operator++() { term_it++; }

void CVC4TermIter::operator++(int junk) { ++term_it; }

const Term CVC4TermIter::operator*() const
{
  Term t(new CVC4Term(*term_it));
  return t;
};

bool CVC4TermIter::operator==(const CVC4TermIter & it)
{
  return term_it == it.term_it;
}

bool CVC4TermIter::operator!=(const CVC4TermIter & it)
{
  return term_it != term_it;
}

bool CVC4TermIter::equal(const TermIterBase & other) const
{
  const CVC4TermIter & cti = static_cast<const CVC4TermIter &>(other);
  return term_it == cti.term_it;
}

/* end CVC4TermIter implementation */

/* CVC4Term implementation */

std::size_t CVC4Term::hash() const
{
  return termhash(term);
}
bool CVC4Term::compare(const Term & absterm) const
{
  std::shared_ptr<CVC4Term> other =
    std::static_pointer_cast<CVC4Term>(absterm);
  return term == other->term;
}
Fun CVC4Term::get_fun() const { throw NotImplementedException("not implemented"); }
Sort CVC4Term::get_sort() const
{
  Sort s(new CVC4Sort(term.getSort()));
  return s;
}
std::string CVC4Term::to_string() const { return term.toString(); }
// TODO: Implement iterator and to_int conversion
uint64_t CVC4Term::to_int() const { throw NotImplementedException("not implemented"); }
/** Iterators for traversing the children
 */
TermIter CVC4Term::begin()
{
  return TermIter(new CVC4TermIter(term.begin()));
}

TermIter CVC4Term::end()
{
  return TermIter(new CVC4TermIter(term.end()));
}

/* end CVC4Term implementation */

}
