/*!
 * \file z3_context.cpp
 * \brief A Z3 context, with what the backend keeps about it
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/z3_context.h"

#include <z3++.h>
#include <z3_version.h>

#include <cstddef>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "smt-switch/exceptions.h"
#include "smt-switch/solver_utils.h"

namespace smt {

namespace {

// Whether Z3 makes the power of two Ints a Real, as before Z3 5.4.0
constexpr bool int_power_is_real =
    Z3_MAJOR_VERSION < 5 || (Z3_MAJOR_VERSION == 5 && Z3_MINOR_VERSION < 4);

}  // namespace

z3::expr Z3Context::add_param(const std::string & name, const z3::sort & sort)
{
  // Z3 gives a constant of the same name and sort back as the same term,
  // so a constant named `name` would be a symbol of that name, and a
  // quantifier over it would bind the symbol.
  z3::expr term(*this, Z3_mk_fresh_const(*this, name.c_str(), sort));
  param_info.emplace(term.id(), Param{ term, name });
  return term;
}

bool Z3Context::is_param(const z3::expr & term) const
{
  return param_info.count(term.id()) != 0;
}

std::string Z3Context::get_param_name(const z3::expr & term) const
{
  return param_info.at(term.id()).name;
}

std::size_t Z3Context::InstanceKeyHash::operator()(
    const InstanceKey & key) const
{
  std::size_t h = std::hash<std::string>{}(key.first);
  for (unsigned id : key.second)
  {
    backend::hash_combine(h, id);
  }
  return h;
}

z3::sort Z3Context::add_instance(const std::string & name,
                                 const std::vector<z3::sort> & params,
                                 const std::string & text)
{
  InstanceKey key{ name, {} };
  key.second.reserve(params.size());
  for (const z3::sort & p : params)
  {
    key.second.push_back(p.id());
  }
  auto it = uninterp_sort_cache.find(key);
  if (it != uninterp_sort_cache.end())
  {
    return it->second;
  }
  std::string symbol = backend::internal_name("sort", count++);
  z3::sort sort = uninterpreted_sort(symbol.c_str());
  uninterp_sort_cache.emplace(std::move(key), sort);
  uninterp_sort_info.emplace(sort.id(), SortInstance{ name, params });
  instance_text.emplace(symbol, text);
  return sort;
}

bool Z3Context::is_instance(const z3::sort & sort) const
{
  return uninterp_sort_info.count(sort.id()) != 0;
}

std::string Z3Context::get_instance_name(const z3::sort & sort) const
{
  auto it = uninterp_sort_info.find(sort.id());
  if (it == uninterp_sort_info.end())
  {
    return sort.name().str();
  }
  return it->second.name;
}

std::vector<z3::sort> Z3Context::get_instance_params(
    const z3::sort & sort) const
{
  auto it = uninterp_sort_info.find(sort.id());
  if (it == uninterp_sort_info.end())
  {
    return {};
  }
  return it->second.params;
}

void Z3Context::add_datatype_name(const std::string & name)
{
  datatype_names.insert(name);
}

bool Z3Context::has_datatype_name(const std::string & name) const
{
  return datatype_names.count(name) != 0;
}

z3::expr Z3Context::make_int_power(const z3::expr & base,
                                   const z3::expr & exponent)
{
  if (!int_power_is_real)
  {
    return z3::pw(base, exponent);
  }
  z3::context & c = *this;
  z3::expr zero = c.int_val(0);
  z3::expr one = c.int_val(1);
  z3::expr minus_one = c.int_val(-1);
  // an integer for a positive exponent, as a Real
  z3::expr power(c, Z3_mk_real2int(c, z3::pw(base, exponent)));
  c.check_error();
  // a negative exponent leaves an integer only for a base of 1 or -1
  return z3::ite(
      exponent >= zero,
      z3::ite(exponent == zero, one, power),
      z3::ite(base == one,
              one,
              z3::ite(base == minus_one,
                      z3::ite(z3::mod(exponent, 2) == zero, one, minus_one),
                      zero)));
}

bool Z3Context::is_int_power(const z3::expr & term)
{
  if (!int_power_is_real || !term.is_app()
      || term.decl().decl_kind() != Z3_OP_ITE)
  {
    return false;
  }
  z3::expr nonnegative = term.arg(0);
  z3::expr negative = term.arg(2);
  if (!nonnegative.is_app() || nonnegative.decl().decl_kind() != Z3_OP_GE
      || !negative.is_app() || negative.decl().decl_kind() != Z3_OP_ITE
      || !negative.arg(0).is_app()
      || negative.arg(0).decl().decl_kind() != Z3_OP_EQ)
  {
    return false;
  }
  z3::expr base = negative.arg(0).arg(0);
  z3::expr exponent = nonnegative.arg(0);
  return base.is_int() && exponent.is_int()
         && z3::eq(term, make_int_power(base, exponent));
}

std::string Z3Context::print_term(const z3::expr & term) const
{
  std::string text = term.to_string();
  if (instance_text.empty())
  {
    return text;
  }
  // Z3 writes an instance as its internal name, a whole unbarred symbol; a
  // barred symbol is a user's name, which may contain one
  std::string_view delimiters = "|() \t\n\r\f\v";
  std::string res;
  res.reserve(text.size());
  std::size_t i = 0;
  while (i < text.size())
  {
    if (text[i] == '|')
    {
      std::size_t end = text.find('|', i + 1);
      end = end == std::string::npos ? text.size() : end + 1;
      res.append(text, i, end - i);
      i = end;
    }
    else if (delimiters.find(text[i]) != std::string_view::npos)
    {
      res += text[i];
      ++i;
    }
    else
    {
      std::size_t end = text.find_first_of(delimiters, i);
      end = end == std::string::npos ? text.size() : end;
      std::string symbol = text.substr(i, end - i);
      auto it = instance_text.find(symbol);
      res += it == instance_text.end() ? symbol : it->second;
      i = end;
    }
  }
  return res;
}

void Z3Context::rethrow(const z3::exception & e) const
{
  // Z3 reports misuse, such as an ill-sorted term or a model asked for
  // after unsat, under Z3_EXCEPTION as well as under the codes named for
  // it, and its own failures under codes of their own. z3++ raises its
  // own checks with no code set.
  Z3_error_code code = Z3_get_error_code(*this);
  switch (code)
  {
    case Z3_OK:
    case Z3_SORT_ERROR:
    case Z3_IOB:
    case Z3_INVALID_ARG:
    case Z3_PARSER_ERROR:
    case Z3_NO_PARSER:
    case Z3_INVALID_PATTERN:
    case Z3_INVALID_USAGE:
    case Z3_EXCEPTION: throw IncorrectUsageException(e.msg());
    case Z3_MEMOUT_FAIL:
    case Z3_INTERNAL_FATAL: throw SolverException(e.msg());
    case Z3_FILE_ACCESS_ERROR: throw SystemException(e.msg());
    case Z3_DEC_REF_ERROR: throw InternalException(e.msg());
  }
  throw InternalException("Z3 reported an unknown error code "
                          + std::to_string(code) + ": " + e.msg());
}

}  // namespace smt
