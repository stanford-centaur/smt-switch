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
#include <utility>
#include <vector>

#include "utils.h"

namespace smt {

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
                                 const std::vector<z3::sort> & params)
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
  z3::sort sort = uninterpreted_sort(internal_name("sort", count++).c_str());
  uninterp_sort_cache.emplace(std::move(key), sort);
  uninterp_sort_info.emplace(sort.id(), SortInstance{ name, params });
  return sort;
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

}  // namespace smt
