#include "logging_term.h"

#include "exceptions.h"
#include "utils.h"

using namespace std;

namespace smt {

/* LoggingTerm */

LoggingTerm::LoggingTerm(Term t, Sort s, Op o, TermVec c)
    : wrapped_term(t), sort(s), op(o), children(c), is_symbol(false)
{
}

LoggingTerm::LoggingTerm(Term t, Sort s, Op o, TermVec c, string r)
    : wrapped_term(t), sort(s), op(o), children(c), repr(r), is_symbol(true)
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
  // compare op
  if (op != lt->op)
  {
    return false;
  }

  // compare underlying term and sort
  // this will handle sort aliasing issues from solvers
  // that don't distinguish between certain sorts
  if (wrapped_term != lt->wrapped_term || sort != lt->sort)
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
      if (children[i] != lt->children[i])
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
  if (is_value())
  {
    // special-case for Bool, because of sort-aliasing
    if (get_sort()->get_sort_kind() == BOOL)
    {
      std::string repr = wrapped_term->to_string();
      // check truthy values
      if (repr == "true" || repr == "#b1" || repr == "(_ bv0 1)")
      {
        return "true";
      }
      else
      {
        // Expect falsey values
        Assert(repr == "false" || repr == "#b0" || repr == "(_ bv0 1)");
        return "false";
      }
    }
    else
    {
      return wrapped_term->to_string();
    }
  }
  else
  {
    // Op should not be null because handled values above
    //     and symbols already have the repr set
    Assert(!get_op().is_null());
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

bool LoggingTerm::is_symbolic_const() const
{
  return is_symbol;
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
