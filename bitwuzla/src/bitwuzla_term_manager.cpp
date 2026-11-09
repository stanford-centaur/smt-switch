/*!
 * \file bitwuzla_term_manager.cpp
 * \brief A Bitwuzla term manager, with what the backend keeps about it.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */

#include "bitwuzla_term_manager.h"

#include <bitwuzla/cpp/bitwuzla.h>

#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <utility>
#include <vector>

#include "utils.h"

namespace smt {

std::size_t BzlaTermManager::InstanceKeyHash::operator()(
    const InstanceKey & key) const
{
  std::size_t h = std::hash<std::uint64_t>{}(key.first);
  for (std::uint64_t id : key.second)
  {
    detail::hash_combine(h, id);
  }
  return h;
}

std::uint64_t BzlaTermManager::add_constructor(const std::string & name,
                                               std::uint64_t arity)
{
  constructors.push_back(SortConstructor{ name, arity });
  return constructors.size() - 1;
}

std::string BzlaTermManager::get_constructor_name(std::uint64_t id) const
{
  return constructors.at(id).name;
}

std::uint64_t BzlaTermManager::get_constructor_arity(std::uint64_t id) const
{
  return constructors.at(id).arity;
}

bitwuzla::Sort BzlaTermManager::add_instance(
    std::uint64_t constructor, const std::vector<bitwuzla::Sort> & params)
{
  InstanceKey key{ constructor, {} };
  key.second.reserve(params.size());
  for (const bitwuzla::Sort & p : params)
  {
    key.second.push_back(p.id());
  }
  auto it = uninterp_sort_cache.find(key);
  if (it != uninterp_sort_cache.end())
  {
    return it->second;
  }
  bitwuzla::Sort sort =
      mk_uninterpreted_sort(internal_name("sort", instance_count++));
  uninterp_sort_cache.emplace(std::move(key), sort);
  uninterp_sort_info.emplace(sort.id(), SortInstance{ constructor, params });
  return sort;
}

std::string BzlaTermManager::get_instance_name(
    const bitwuzla::Sort & sort) const
{
  auto it = uninterp_sort_info.find(sort.id());
  if (it == uninterp_sort_info.end())
  {
    return sort.uninterpreted_symbol().value_or("");
  }
  return get_constructor_name(it->second.constructor);
}

std::vector<bitwuzla::Sort> BzlaTermManager::get_instance_params(
    const bitwuzla::Sort & sort) const
{
  auto it = uninterp_sort_info.find(sort.id());
  if (it == uninterp_sort_info.end())
  {
    return {};
  }
  return it->second.params;
}

}  // namespace smt
