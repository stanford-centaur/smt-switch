#include "z3_sort.h"
#include <sstream>
#include "exceptions.h"

using namespace std;

namespace smt {

// Z3Sort implementation

std::size_t Z3Sort::hash() const
{
throw NotImplementedException(
      "Term iteration not implemented for Z3 backend.");
}

uint64_t Z3Sort::get_width() const
{
throw NotImplementedException(
      "Term iteration not implemented for Z3 backend.");
}

Sort Z3Sort::get_indexsort() const
{
throw NotImplementedException(
      "Term iteration not implemented for Z3 backend.");

}

Sort Z3Sort::get_elemsort() const
{
throw NotImplementedException(
      "Term iteration not implemented for Z3 backend.");
}

SortVec Z3Sort::get_domain_sorts() const
{
    throw NotImplementedException(
      "Term iteration not implemented for Z3 backend.");
}

Sort Z3Sort::get_codomain_sort() const
{
    throw NotImplementedException(
      "Term iteration not implemented for Z3 backend.");
}

string Z3Sort::get_uninterpreted_name() const
{
  throw NotImplementedException(
      "get_uninterpreted_name not implemented for Z3Sort");
}

size_t Z3Sort::get_arity() const
{
  throw NotImplementedException(
      "Z3 does not support uninterpreted sort constructors");
}

SortVec Z3Sort::get_uninterpreted_param_sorts() const
{
  throw NotImplementedException(
      "Z3 does not support uninterpreted sort constructors");
}

Datatype Z3Sort::get_datatype() const
{
  throw NotImplementedException("get_datatype");
};

bool Z3Sort::compare(const Sort s) const
{

throw NotImplementedException(
      "Term iteration not implemented for Z3 backend.");
}

SortKind Z3Sort::get_sort_kind() const
{
throw NotImplementedException(
      "Term iteration not implemented for Z3 backend.");
}

}  // namespace smt
