#include "z3_sort.h"

#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <utility>

#include "exceptions.h"
#include "utils.h"
#include "z3_datatype.h"

using namespace std;

namespace smt {

// Z3Sort implementation

Z3Sort::Z3Sort(const std::shared_ptr<Z3Context> & c, z3::sort z3sort)
    : ctx(c), type(z3sort), z_func(*c)
{
}

Z3Sort::Z3Sort(const std::shared_ptr<Z3Context> & c, z3::func_decl zfunc)
    : ctx(c), type(*c), z_func(zfunc), is_function(true)
{
}

Z3Sort::Z3Sort(const std::shared_ptr<Z3Context> & c,
               std::string name,
               std::uint64_t arity)
    : ctx(c),
      type(*c),
      z_func(*c),
      is_constructor(true),
      constructor_name(std::move(name)),
      constructor_arity(arity)
{
}

std::size_t Z3Sort::hash() const
{
  // Z3 numbers sorts per context, so start from the context, as compare
  // tells apart sorts of different contexts
  std::size_t h = std::hash<Z3Context *>{}(ctx.get());
  if (is_constructor)
  {
    detail::hash_combine(h, std::hash<std::string>{}(constructor_name));
    detail::hash_combine(h, constructor_arity);
  }
  else if (is_function)
  {
    // a function sort is held as a func_decl, but its name is not part of
    // the sort, so hash only the signature, to agree with compare
    detail::hash_combine(h, z_func.range().id());
    for (unsigned i = 0; i < z_func.arity(); i++)
    {
      detail::hash_combine(h, z_func.domain(i).id());
    }
  }
  else
  {
    // unique within the context, unlike Z3's structural hash
    detail::hash_combine(h, type.id());
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
  SortKind sk = get_sort_kind();
  if (sk == UNINTERPRETED_CONS)
  {
    return constructor_name;
  }
  if (sk == UNINTERPRETED)
  {
    // an applied sort is named after its constructor, not its Z3 sort
    return ctx->get_instance_name(type);
  }
  throw IncorrectUsageException("Sort of kind " + smt::to_string(sk)
                                + " has no uninterpreted name");
}

size_t Z3Sort::get_arity() const
{
  SortKind sk = get_sort_kind();
  if (sk == UNINTERPRETED_CONS)
  {
    return constructor_arity;
  }
  if (sk == UNINTERPRETED)
  {
    return 0;
  }
  throw IncorrectUsageException("Sort of kind " + smt::to_string(sk)
                                + " has no arity");
}

SortVec Z3Sort::get_uninterpreted_param_sorts() const
{
  if (get_sort_kind() != UNINTERPRETED)
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no uninterpreted param sorts");
  }
  auto z3_params = ctx->get_instance_params(type);
  SortVec params;
  params.reserve(z3_params.size());
  for (const z3::sort & p : z3_params)
  {
    params.push_back(std::make_shared<Z3Sort>(ctx, p));
  }
  return params;
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
  if (!zs || is_function != zs->is_function
      || is_constructor != zs->is_constructor)
  {
    return false;
  }
  if (is_constructor)
  {
    // Z3 gives the same sort back for the same name, so constructors of the
    // same name and arity are the same constructor
    return ctx == zs->ctx && constructor_name == zs->constructor_name
           && constructor_arity == zs->constructor_arity;
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
  if (is_constructor)
  {
    return UNINTERPRETED_CONS;
  }
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
    Z3_decl_kind kind = z_func.decl_kind();
    if (kind == Z3_OP_DT_CONSTRUCTOR)
    {
      return CONSTRUCTOR;
    }
    else if (kind == Z3_OP_DT_ACCESSOR)
    {
      return SELECTOR;
    }
    else if (kind == Z3_OP_DT_IS)
    {
      return TESTER;
    }
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
  if (is_constructor)
  {
    throw IncorrectUsageException("Sort constructor " + constructor_name
                                  + " is not a term sort until it is applied");
  }
  return type;
}

}  // namespace smt
