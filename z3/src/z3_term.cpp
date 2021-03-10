#include "z3_term.h"

#include <unordered_map>

#include "exceptions.h"
#include "ops.h"
#include "z3_sort.h"

using namespace std;

namespace smt {

// Z3TermIter implementation

// Z3TermIter::Z3TermIter(const Z3TermIter & it)
// {
//   throw NotImplementedException(
//       "Term iteration not implemented for Z3 backend.");
// }

Z3TermIter & Z3TermIter::operator=(const Z3TermIter & it)
{
  throw NotImplementedException(
      "Term iteration not implemented for Z3 backend.");
}

void Z3TermIter::operator++()
{
  throw NotImplementedException(
      "Term iteration not implemented for Z3 backend.");
}

const Term Z3TermIter::operator*()
{
  throw NotImplementedException(
      "Term iteration not implemented for Z3 backend.");
}

TermIterBase * Z3TermIter::clone() const
{
  throw NotImplementedException(
      "Term iteration not implemented for Z3 backend.");
}

bool Z3TermIter::operator==(const Z3TermIter & it)
{
  throw NotImplementedException(
      "Term iteration not implemented for Z3 backend.");
}

bool Z3TermIter::operator!=(const Z3TermIter & it)
{
  throw NotImplementedException(
      "Term iteration not implemented for Z3 backend.");
}

bool Z3TermIter::equal(const TermIterBase & other) const
{
  throw NotImplementedException(
      "Term iteration not implemented for Z3 backend.");
}

// end Z3TermIter implementation

// Z3Term implementation

size_t Z3Term::hash() const
{
  if (!is_function)
  {
    return term.hash();
  }
  else
  {
    return z_func.hash();
  }
}

std::size_t Z3Term::get_id() const
{
  if (!is_function)
  {
    return term.id();
  }
  else
  {
    return z_func.id();
  }
}

bool Z3Term::compare(const Term & absterm) const
{
  std::shared_ptr<Z3Term> zs = std::static_pointer_cast<Z3Term>(absterm);
  if (is_function && zs->is_function)
  {
    return z_func.hash() == (zs->z_func).hash();
  }
  else if (!is_function && !zs->is_function)
  {
    return term.hash() == (zs->term).hash();
  }
  return false;
}

Op Z3Term::get_op() const
{
  throw NotImplementedException("get_op not yet implemented.");
}

Sort Z3Term::get_sort() const
{
  return std::make_shared<Z3Sort>(term.get_sort(), *ctx);
}

bool Z3Term::is_symbol() const { return (term.is_const() || term.is_var()); }

bool Z3Term::is_param() const { return term.is_var(); }

bool Z3Term::is_symbolic_const() const
{
  return (term.is_const() && !is_function);
}

bool Z3Term::is_value() const
{
  throw NotImplementedException("is_value not implemented for Z3 backend.");
}

string Z3Term::to_string()
{
  if (is_function)
  {
    return z_func.to_string();
  }
  else
  {
    return term.to_string();
  }
}

uint64_t Z3Term::to_int() const
{
  std::string val = term.to_string();
  int base = 10;

  // Process bit-vector format.
  if (term.is_bv())
  {
    if (val.substr(0, 2) == "#x")
    {
      base = 16;
    }
    else if (val.substr(0, 2) == "#b")
    {
      base = 2;
    }
    else
    {
      std::string msg = val;
      msg += " is not a value term, can't convert to int.";
      throw IncorrectUsageException(msg.c_str());
    }
    val = val.substr(2, val.length());
    val = val.substr(0, val.find(" "));
  }

  // If not bit-vector, try parsing an int from the term.
  try
  {
    return std::stoi(val, nullptr, base);
  }
  catch (std::exception const & e)
  {
    std::string msg("Term ");
    msg += val;
    msg += " does not contain an integer representable by a machine int.";
    throw IncorrectUsageException(msg.c_str());
  }
}

TermIter Z3Term::begin()
{
  throw NotImplementedException("begin not implemented for Z3 backend.");
}

TermIter Z3Term::end()
{
  throw NotImplementedException("end not implemented for Z3 backend.");
}

std::string Z3Term::print_value_as(SortKind sk)
{
  if (!is_value())
  {
    throw IncorrectUsageException(
        "Cannot use print_value_as on a non-value term.");
  }
  return term.to_string();
}

// string Z3Term::const_to_string() const {
//	return term.to_string();
//}

// end Z3Term implementation

}  // namespace smt