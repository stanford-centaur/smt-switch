/*!
 * \file msat_env.cpp
 * \brief A MathSAT environment, with what the backend keeps about it.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */

#include "msat_env.h"

#include <mathsat.h>

#include <cstddef>
#include <functional>
#include <string>
#include <utility>
#include <vector>

#include "msat_extensions.h"
#include "utils.h"

namespace smt {

MsatEnv::MsatEnv(msat_env env, msat_config config) : msat_env(env), cfg(config)
{
}

MsatEnv::~MsatEnv()
{
  msat_destroy_env(*this);
  msat_destroy_config(cfg);
}

std::size_t MsatEnv::InstanceKeyHash::operator()(const InstanceKey & key) const
{
  std::size_t h = std::hash<std::string>{}(key.first);
  for (std::size_t id : key.second)
  {
    detail::hash_combine(h, id);
  }
  return h;
}

msat_type MsatEnv::add_instance(const std::string & name,
                                const std::vector<msat_type> & params)
{
  InstanceKey key{ name, {} };
  key.second.reserve(params.size());
  for (msat_type p : params)
  {
    key.second.push_back(msat_type_id(p));
  }
  auto it = uninterp_sort_cache.find(key);
  if (it != uninterp_sort_cache.end())
  {
    return it->second;
  }
  msat_type t =
      msat_get_simple_type(*this, internal_name("sort", count++).c_str());
  uninterp_sort_cache.emplace(std::move(key), t);
  uninterp_sort_info.emplace(msat_type_id(t), SortInstance{ name, params });
  return t;
}

bool MsatEnv::is_instance(msat_type t) const
{
  return uninterp_sort_info.count(msat_type_id(t)) != 0;
}

std::string MsatEnv::get_instance_name(msat_type t) const
{
  auto it = uninterp_sort_info.find(msat_type_id(t));
  if (it == uninterp_sort_info.end())
  {
    return detail::get_msat_string(msat_type_repr(t));
  }
  return it->second.name;
}

std::vector<msat_type> MsatEnv::get_instance_params(msat_type t) const
{
  auto it = uninterp_sort_info.find(msat_type_id(t));
  if (it == uninterp_sort_info.end())
  {
    return {};
  }
  return it->second.params;
}

}  // namespace smt
