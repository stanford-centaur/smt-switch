#include "z3_term.h"
#include "exceptions.h"
#include "ops.h"
#include "z3_sort.h"

#include <unordered_map>

using namespace std;

namespace smt {

// Z3TermIter implementation

Z3TermIter::Z3TermIter(const Z3TermIter & it)
{
  throw NotImplementedException(
      "Term iteration not implemented for Yices backend.");
}

Z3TermIter & Z3TermIter::operator=(const Z3TermIter & it)
{
  throw NotImplementedException(
      "Term iteration not implemented for Yices backend.");
}

void Z3TermIter::operator++()
{
  throw NotImplementedException(
      "Term iteration not implemented for Yices backend.");
}

const Term Z3TermIter::operator*()
{
  throw NotImplementedException(
      "Term iteration not implemented for Yices backend.");
}

TermIterBase * Z3TermIter::clone() const
{
  throw NotImplementedException(
      "Term iteration not implemented for Yices backend.");
}

bool Z3TermIter::operator==(const Z3TermIter & it)
{
  throw NotImplementedException(
      "Term iteration not implemented for Yices backend.");
}

bool Z3TermIter::operator!=(const Z3TermIter & it)
{
  throw NotImplementedException(
      "Term iteration not implemented for Yices backend.");
}

bool Z3TermIter::equal(const TermIterBase & other) const
{
  throw NotImplementedException(
      "Term iteration not implemented for Yices backend.");
}

// end Z3TermIter implementation

// Z3Term implementation

size_t Z3Term::hash() const
{
throw NotImplementedException(
      "Term iteration not implemented for Yices backend.");
}

bool Z3Term::compare(const Term & absterm) const
{
throw NotImplementedException(
      "Term iteration not implemented for Yices backend.");
}

Op Z3Term::get_op() const
{
throw NotImplementedException(
      "Term iteration not implemented for Yices backend.");
}

Sort Z3Term::get_sort() const
{
throw NotImplementedException(
      "Term iteration not implemented for Yices backend.");
}

bool Z3Term::is_symbol() const
{
throw NotImplementedException(
      "Term iteration not implemented for Yices backend.");
}

bool Z3Term::is_param() const
{
  throw NotImplementedException("Z3 backend does not support parameters yet.");
}

bool Z3Term::is_symbolic_const() const
{
throw NotImplementedException(
      "Term iteration not implemented for Yices backend.");
}

bool Z3Term::is_value() const
{
throw NotImplementedException(
      "Term iteration not implemented for Yices backend.");
}

string Z3Term::to_string() {
throw NotImplementedException(
      "Term iteration not implemented for Yices backend."); }

uint64_t Z3Term::to_int() const
{
    throw NotImplementedException(
      "Term iteration not implemented for Yices backend.");
}

TermIter Z3Term::begin()
{
  throw NotImplementedException(
      "Term iteration not implemented for Yices backend.");
}

TermIter Z3Term::end()
{
  throw NotImplementedException(
      "Term iteration not implemented for Yices backend.");
}

std::string Z3Term::print_value_as(SortKind sk)
{
throw NotImplementedException(
      "Term iteration not implemented for Yices backend.");
}

string Z3Term::const_to_string() const
{
throw NotImplementedException(
      "Term iteration not implemented for Yices backend.");
}

// end Z3Term implementation

}  // namespace smt
