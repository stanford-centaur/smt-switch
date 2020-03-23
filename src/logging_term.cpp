#include "logging_term.h"

#include "exceptions.h"

using namespace std;

namespace smt {

/* LoggingTerm */

LoggingTerm::LoggingTerm(Term t, Sort s, Op o, TermVec c)
    : term(t), sort(s), op(o), children(c)
{
}

LoggingTerm::~LoggingTerm() {}

// implemented
bool LoggingTerm::compare(const Term & t) const
{
  shared_ptr<LoggingTerm> lt = static_pointer_cast<LoggingTerm>(t);
  // compare underlying term and sort
  // this will handle sort aliasing issues from solvers
  // that don't distinguish between certain sorts
  return (term == lt->term) && (sort == lt->sort);
}

Op LoggingTerm::get_op() const { return op; }

Sort LoggingTerm::get_sort() const { return sort; }

string LoggingTerm::to_string()
{
  throw NotImplementedException("Logging term doesn't have to_string yet.");
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

size_t LoggingTerm::hash() const { return term->hash(); }

bool LoggingTerm::is_symbolic_const() const
{
  return term->is_symbolic_const();
}

bool LoggingTerm::is_value() const { return term->is_value(); }

uint64_t LoggingTerm::to_int() const { return term->to_int(); }

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
