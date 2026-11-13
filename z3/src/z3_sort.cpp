/*!
 * \file z3_sort.cpp
 * \brief Z3 implementation of AbsSort
 * \author Lindsey Stuntz
 * \author Áron Ricardo Perez-Lopez
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/z3_sort.h"

#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <utility>

#include "smt-switch/exceptions.h"
#include "smt-switch/utils.h"
#include "smt-switch/z3_datatype.h"

namespace smt {

// Z3Sort implementation

Z3Sort::Z3Sort(const std::shared_ptr<Z3Context> & c, z3::sort z3sort)
    : ctx(c), type(z3sort), range(*c)
{
}

Z3Sort::Z3Sort(const std::shared_ptr<Z3Context> & c, z3::func_decl zfunc)
    : ctx(c), type(*c), function_kind(FUNCTION), range(zfunc.range())
{
  domain.reserve(zfunc.arity());
  for (unsigned i = 0; i < zfunc.arity(); i++)
  {
    domain.push_back(zfunc.domain(i));
  }
  Z3_decl_kind kind = zfunc.decl_kind();
  if (kind == Z3_OP_DT_CONSTRUCTOR)
  {
    function_kind = CONSTRUCTOR;
  }
  else if (kind == Z3_OP_DT_ACCESSOR)
  {
    function_kind = SELECTOR;
  }
  else if (kind == Z3_OP_DT_IS)
  {
    function_kind = TESTER;
  }
}

Z3Sort::Z3Sort(const std::shared_ptr<Z3Context> & c,
               std::vector<z3::sort> domain_sorts,
               z3::sort codomain)
    : ctx(c),
      type(*c),
      function_kind(FUNCTION),
      domain(std::move(domain_sorts)),
      range(std::move(codomain))
{
}

Z3Sort::Z3Sort(const std::shared_ptr<Z3Context> & c,
               std::string name,
               std::uint64_t arity)
    : ctx(c),
      type(*c),
      range(*c),
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
  else if (function_kind.has_value())
  {
    // hash only the signature, to agree with compare
    detail::hash_combine(h, range.id());
    for (const z3::sort & d : domain)
    {
      detail::hash_combine(h, d.id());
    }
  }
  else
  {
    // unique within the context, unlike Z3's structural hash
    detail::hash_combine(h, type.id());
  }
  return h;
}

std::uint64_t Z3Sort::get_width() const
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
  if (!function_kind.has_value())
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no domain sorts");
  }
  SortVec sorts;
  sorts.reserve(domain.size());
  for (const z3::sort & d : domain)
  {
    sorts.push_back(std::make_shared<Z3Sort>(ctx, d));
  }
  return sorts;
}

Sort Z3Sort::get_codomain_sort() const
{
  if (!function_kind.has_value())
  {
    throw IncorrectUsageException("Sort of kind "
                                  + smt::to_string(get_sort_kind())
                                  + " has no codomain sort");
  }
  return std::make_shared<Z3Sort>(ctx, range);
}

std::string Z3Sort::get_uninterpreted_name() const
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

std::size_t Z3Sort::get_arity() const
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

Sort Z3Sort::get_uninterpreted_constructor() const
{
  if (get_sort_kind() != UNINTERPRETED || !ctx->is_instance(type))
  {
    throw IncorrectUsageException("Sort " + to_string()
                                  + " was not made by applying a sort "
                                    "constructor");
  }
  // Z3 gives the same sort back for the same name, so a constructor is its
  // name and arity
  return std::make_shared<Z3Sort>(
      ctx, ctx->get_instance_name(type), ctx->get_instance_params(type).size());
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
  if (!zs || function_kind.has_value() != zs->function_kind.has_value()
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
  if (!function_kind.has_value())
  {
    return z3::eq(type, zs->type);
  }

  // compare function sorts by signature
  if (domain.size() != zs->domain.size() || !z3::eq(range, zs->range))
  {
    return false;
  }
  for (std::size_t i = 0; i < domain.size(); i++)
  {
    if (!z3::eq(domain[i], zs->domain[i]))
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
  else if (function_kind.has_value())
  {
    return *function_kind;
  }
  else
  {
    throw NotImplementedException("smt-switch has no SortKind for the Z3 sort "
                                  + type.to_string());
  }
}

z3::sort Z3Sort::get_z3_type() const
{
  if (function_kind.has_value())
  {
    throw IncorrectUsageException("Can't get a Z3 sort from a function sort");
  }
  if (is_constructor)
  {
    throw IncorrectUsageException("Sort constructor " + constructor_name
                                  + " is not a term sort until it is applied");
  }
  return type;
}

}  // namespace smt
