#include "logging_term.h"

#include "exceptions.h"

using namespace std;

namespace smt {

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
  return (term == t.term) && (sort == t.sort);
}

Op LoggingTerm::get_op() const { return op; }

Sort LoggingTerm::get_sort() const { return sort; }

string LoggingTerm::to_string() const
{
  throw NotImplementedException("Logging term doesn't have to_string yet.");
}

TermIter begin()
{
  throw NotImplementedException("LoggingTerm doesn't have term iteration yet");
}

TermIter end()
{
  throw NotImplementedException("LoggingTerm doesn't have term iteration yet");
}

// dispatched to underlying term

size_t LoggingTerm::hash() const { return term->hash(); }

bool LoggingTerm::is_symbolic_const() const
{
  return term->is_symbolic_const();
}

bool LoggingTerm::is_value() const { return term->is_value(); }

uint64_t LoggingTerm::to_int() const { return term->to_int(); }

}  // namespace smt
