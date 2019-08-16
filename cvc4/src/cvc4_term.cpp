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

Op CVC4Term::get_op() const { throw NotImplementedException("not implemented"); }

Sort CVC4Term::get_sort() const
{
  Sort s(new CVC4Sort(term.getSort()));
  return s;
}

bool CVC4Term::is_symbolic_const() const
{
  return (term.getKind() == ::CVC4::api::CONSTANT);
}

bool CVC4Term::is_value() const
{
  // checking all possible const types for future-proofing
  // not all these sorts are even supported at this time
  ::CVC4::api::Kind k = term.getKind();
  return ((k == ::CVC4::api::CONST_BOOLEAN)
          || (k == ::CVC4::api::CONST_BITVECTOR)
          || (k == ::CVC4::api::CONST_RATIONAL)
          || (k == ::CVC4::api::CONST_FLOATINGPOINT)
          || (k == ::CVC4::api::CONST_ROUNDINGMODE)
          || (k == ::CVC4::api::CONST_STRING));
}

std::string CVC4Term::to_string() const { return term.toString(); }

uint64_t CVC4Term::to_int() const
{
  std::string val = term.toString();
  ::CVC4::api::Sort sort = term.getSort();

  // process smt-lib bit-vector format
  if (sort.isBitVector())
  {
    if (val.find("(_ bv") == std::string::npos)
    {
      std::string msg = val;
      msg += " is not a constant term, can't convert to int.";
      throw IncorrectUsageException(msg.c_str());
    }
    val = val.substr(5, val.length());
    val = val.substr(0, val.find(" "));
  }

  try
  {
    return std::stoi(val);
  }
  catch (std::exception const & e)
  {
    std::string msg("Term ");
    msg += val;
    msg += " does not contain an integer representable by a machine int.";
    throw IncorrectUsageException(msg.c_str());
  }
}

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
