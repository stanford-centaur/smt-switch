#include "z3_sort.h"

#include <cstdint>
#include <sstream>

#include "exceptions.h"
#include "z3_datatype.h"

using namespace std;

namespace smt {

// Z3Sort implementation

std::size_t Z3Sort::hash() const
{
  if (is_function)
  {
    // a function sort is held as a func_decl, but its name is not part of
    // the sort, so hash only the signature, to agree with compare
    std::size_t h = z_func.range().hash();
    for (unsigned i = 0; i < z_func.arity(); i++)
    {
      // Boost's hash_combine: 0x9e3779b9 is 2^32 / golden ratio, whose
      // irregular bits spread the value; the shifts mix in the hash so
      // far, so argument order matters and equal sorts don't cancel out
      h ^= z_func.domain(i).hash() + 0x9e3779b9 + (h << 6) + (h >> 2);
    }
    return h;
  }
  return type.hash();
}

uint64_t Z3Sort::get_width() const
{
  if (type.is_bv())
  {
    return type.bv_size();
  }
  else
  {
    throw IncorrectUsageException("Can only get width from bit-vector sort");
  }
}

Sort Z3Sort::get_indexsort() const
{
  if (type.is_array())
  {
    return std::make_shared<Z3Sort>(type.array_domain(), *ctx);
  }
  else
  {
    throw IncorrectUsageException("Can only get width from bit-vector sort");
  }
}

Sort Z3Sort::get_elemsort() const
{
  if (type.is_array())
  {
    return std::make_shared<Z3Sort>(type.array_range(), *ctx);
  }
  else
  {
    throw IncorrectUsageException("Can only get elemsort from array sort");
  }
}

SortVec Z3Sort::get_domain_sorts() const
{
  if (is_function)
  {
    unsigned s_arity = z_func.arity();
    SortVec sorts;
    sorts.reserve(s_arity);
    Sort s;

    for (unsigned i = 0; i < s_arity; i++)
    {
      s.reset(new Z3Sort(z_func.domain(i), *ctx));
      sorts.push_back(s);
    }

    return sorts;
  }
  else
  {
    throw IncorrectUsageException(
        "Can only get domain sorts from function sort");
  }
}

Sort Z3Sort::get_codomain_sort() const
{
  if (is_function)
  {
    return std::make_shared<Z3Sort>(z_func.range(), *ctx);
  }
  else
  {
    throw IncorrectUsageException(
        "Can only get codomain sort from function sort");
  }
}

string Z3Sort::get_uninterpreted_name() const
{
  if (type.sort_kind() == Z3_UNINTERPRETED_SORT)
  {
    return type.name().str();
  }
  else
  {
    throw IncorrectUsageException(
        "Can only get uninterpreted name from uninterpreted sort");
  }
  return type.name().str();
}

size_t Z3Sort::get_arity() const
{
  if (is_function)
  {
    return z_func.arity();
  }
  else
  {
    return 0;
  }
}

SortVec Z3Sort::get_uninterpreted_param_sorts() const
{
  throw NotImplementedException(
      "get_uninterpreted_param_sorts not implemented for Z3 backend.");
}

Datatype Z3Sort::get_datatype() const
{
  if (type.is_datatype())
    return std::make_shared<Z3Datatype>(*ctx, type);
  else
    throw InternalSolverException("Sort is not datatype");
};

bool Z3Sort::compare(const Sort & s) const
{
  std::shared_ptr<Z3Sort> zs = std::static_pointer_cast<Z3Sort>(s);
  if (is_function != zs->is_function)
  {
    return false;
  }
  if (!is_function)
  {
    return z3::eq(type, zs->type);
  }

  // compare function sorts by signature: the func_decls have different
  // names when one comes from make_sort and the other from a symbol
  const func_decl & other = zs->z_func;
  if (z_func.arity() != other.arity() || !z3::eq(z_func.range(), other.range()))
  {
    return false;
  }
  for (unsigned i = 0; i < z_func.arity(); i++)
  {
    if (!z3::eq(z_func.domain(i), other.domain(i)))
    {
      return false;
    }
  }
  return true;
}

SortKind Z3Sort::get_sort_kind() const
{
  if (type.is_int())
  {
    return INT;
  }
  else if (type.is_real())
  {
    return REAL;
  }
  else if (type.is_bool())
  {
    return BOOL;
  }
  else if (type.is_bv())
  {
    return BV;
  }
  else if (type.is_array())
  {
    return ARRAY;
  }
  else if (type.is_datatype())
  {
    return DATATYPE;
  }
  else if (type.sort_kind() == Z3_UNINTERPRETED_SORT)
  {
    return UNINTERPRETED;
  }
  else if (is_function)
  {
    return FUNCTION;
  }
  else
  {
    std::string msg("Unknown Z3 type");
    throw NotImplementedException(msg.c_str());
  }
}

z3::sort Z3Sort::get_z3_type()
{
  if (is_function)
  {
    throw IncorrectUsageException("Cannot get Z3 type from function term.");
  }
  return type;
}

}  // namespace smt
