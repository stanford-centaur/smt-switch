/*!
 * \file z3_context.cpp
 * \brief A Z3 context, with what the backend keeps about it.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */

#include "z3_context.h"

#include <z3++.h>

#include <cstddef>
#include <functional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "utils.h"

namespace smt {

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
    detail::hash_combine(h, id);
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
  std::string symbol = internal_name("sort", count++);
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

}  // namespace smt
