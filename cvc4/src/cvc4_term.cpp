#include "api/cvc4cpp.h"

#include "exceptions.h"

#include "cvc4_sort.h"
#include "cvc4_term.h"

namespace smt {

// TODO: Figure out how to use this -- can we just instantiate it once?
CVC4::api::TermHashFunction termhash;

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
TermIter CVC4Term::begin() { throw NotImplementedException("not implemented"); }
TermIter CVC4Term::end() { throw NotImplementedException("not implemented"); };

}
