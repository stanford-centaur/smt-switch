#include "z3_sort.h"

#include <cstddef>
#include <cstdint>
#include <functional>

#include "exceptions.h"
#include "z3_datatype.h"

using namespace std;

namespace smt {

// Z3Sort implementation

Z3Sort::Z3Sort(const std::shared_ptr<z3::context> & c, z3::sort z3sort)
    : ctx(c), type(z3sort), z_func(*c)
{
}

Z3Sort::Z3Sort(const std::shared_ptr<z3::context> & c, z3::func_decl zfunc)
    : ctx(c), type(*c), z_func(zfunc), is_function(true)
{
}

std::size_t Z3Sort::hash() const
{
  // Z3 numbers sorts per context, so start from the context, as compare
  // tells apart sorts of different contexts
  std::size_t h = std::hash<z3::context *>{}(ctx.get());
  // Boost's hash_combine: 0x9e3779b9 is 2^32 / golden ratio, whose
  // irregular bits spread the value; the shifts mix in the hash so far,
  // so argument order matters and equal sorts don't cancel out
  auto combine = [&h](std::size_t v) {
    h ^= v + 0x9e3779b9 + (h << 6) + (h >> 2);
  };
  if (is_function)
  {
    // a function sort is held as a func_decl, but its name is not part of
    // the sort, so hash only the signature, to agree with compare
    combine(z_func.range().id());
    for (unsigned i = 0; i < z_func.arity(); i++)
    {
      combine(z_func.domain(i).id());
    }
  }
  else
  {
    // unique within the context, unlike Z3's structural hash
    combine(type.id());
  }
  return h;
}

uint64_t Z3Sort::get_width() const
{
  if (!type.is_bv())
  {
    throw IncorrectUsageException(
        "Sort of kind " + smt::to_string(get_sort_kind()) + " has no width");
  }
  return type.bv_size();
}

Sort Z3Sort::get_indexsort() const
{
  if (!type.is_array())
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no index sort");
  }
  return std::make_shared<Z3Sort>(ctx, type.array_domain());
}

Sort Z3Sort::get_elemsort() const
{
  if (!type.is_array())
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no element sort");
  }
  return std::make_shared<Z3Sort>(ctx, type.array_range());
}

SortVec Z3Sort::get_domain_sorts() const
{
  if (!is_function)
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no domain sorts");
  }
  unsigned s_arity = z_func.arity();
  SortVec sorts;
  sorts.reserve(s_arity);
  Sort s;

  for (unsigned i = 0; i < s_arity; i++)
  {
    s.reset(new Z3Sort(ctx, z_func.domain(i)));
    sorts.push_back(s);
  }

  return sorts;
}

Sort Z3Sort::get_codomain_sort() const
{
  if (!is_function)
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no codomain sort");
  }
  return std::make_shared<Z3Sort>(ctx, z_func.range());
}

string Z3Sort::get_uninterpreted_name() const
{
  if (get_sort_kind() != UNINTERPRETED)
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no uninterpreted name");
  }
  return type.name().str();
}

size_t Z3Sort::get_arity() const
{
  if (get_sort_kind() != UNINTERPRETED)
  {
    throw IncorrectUsageException(
        "Sort of kind " + smt::to_string(get_sort_kind()) + " has no arity");
  }
  // the backend makes no sort constructors, so every arity is zero
  return 0;
}

SortVec Z3Sort::get_uninterpreted_param_sorts() const
{
  if (get_sort_kind() != UNINTERPRETED)
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no uninterpreted param sorts");
  }
  // the backend makes no sort constructors, so no sort has parameters
  return {};
}

Datatype Z3Sort::get_datatype() const
{
  return std::make_shared<Z3Datatype>(ctx, get_z3_datatype());
}

z3::sort Z3Sort::get_z3_datatype() const
{
  if (!type.is_datatype())
  {
    throw IncorrectUsageException(
        "Sort of kind " + smt::to_string(get_sort_kind()) + " has no datatype");
  }
  return type;
}

bool Z3Sort::compare(const Sort & s) const
{
  std::shared_ptr<Z3Sort> zs = std::dynamic_pointer_cast<Z3Sort>(s);
  if (!zs || is_function != zs->is_function)
  {
    return false;
  }
  if (!is_function)
  {
    return z3::eq(type, zs->type);
  }

  // compare function sorts by signature: the func_decls have different
  // names when one comes from make_sort and the other from a symbol
  const z3::func_decl & other = zs->z_func;
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

z3::sort Z3Sort::get_z3_type() const
{
  if (is_function)
  {
    throw IncorrectUsageException("Cannot get Z3 type from function term.");
  }
  return type;
}

}  // namespace smt
