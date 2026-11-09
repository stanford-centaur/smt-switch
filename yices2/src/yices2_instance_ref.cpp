/*!
 * \file yices2_instance_ref.cpp
 * \brief Counts the references to the Yices instance, setting it up for the
 *        first and freeing it after the last.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */

#include "yices2_instance_ref.h"

#include <gmp.h>  // IWYU pragma: keep (required by yices.h)
#include <yices.h>

#include <cstddef>
#include <cstdint>
#include <mutex>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace smt {

namespace {

// Locked around every count change, including the yices_init() and
// yices_exit() calls, so no thread sees Yices half set up. Never destroyed,
// so that a reference released during exit can still lock it.
std::mutex & count_mutex()
{
  static std::mutex & mutex = *new std::mutex;
  return mutex;
}

struct SortConstructor
{
  std::string name;
  std::uint32_t arity;
};

struct SortInstance
{
  std::int32_t constructor_id;
  std::vector<type_t> params;
};

std::size_t count = 0;
// the symbols declared with a function sort, the sort constructors and their
// instances, also under count_mutex, made and freed with the instance
std::unordered_set<term_t> * functions = nullptr;
std::unordered_map<std::int32_t, SortConstructor> * constructors = nullptr;
std::unordered_map<type_t, SortInstance> * instances = nullptr;

void acquire()
{
  std::lock_guard lock(count_mutex());
  if (count++ == 0)
  {
    yices_init();
    functions = new std::unordered_set<term_t>;
    constructors = new std::unordered_map<std::int32_t, SortConstructor>;
    instances = new std::unordered_map<type_t, SortInstance>;
  }
}

}  // namespace

Yices2InstanceRef::Yices2InstanceRef() { acquire(); }

Yices2InstanceRef::Yices2InstanceRef(const Yices2InstanceRef &) { acquire(); }

Yices2InstanceRef::~Yices2InstanceRef()
{
  std::lock_guard lock(count_mutex());
  if (--count == 0)
  {
    yices_exit();
    delete functions;
    functions = nullptr;
    delete constructors;
    constructors = nullptr;
    delete instances;
    instances = nullptr;
  }
}

void Yices2InstanceRef::mark_function(term_t t)
{
  std::lock_guard lock(count_mutex());
  functions->insert(t);
}

bool Yices2InstanceRef::is_function(term_t t)
{
  std::lock_guard lock(count_mutex());
  return functions->count(t) != 0;
}

void Yices2InstanceRef::add_constructor(std::int32_t id,
                                        const std::string & name,
                                        std::uint32_t arity)
{
  std::lock_guard lock(count_mutex());
  constructors->insert_or_assign(id, SortConstructor{ name, arity });
}

std::string Yices2InstanceRef::get_constructor_name(std::int32_t id)
{
  std::lock_guard lock(count_mutex());
  return constructors->at(id).name;
}

std::uint32_t Yices2InstanceRef::get_constructor_arity(std::int32_t id)
{
  std::lock_guard lock(count_mutex());
  return constructors->at(id).arity;
}

void Yices2InstanceRef::add_instance(type_t t,
                                     std::int32_t constructor_id,
                                     const std::vector<type_t> & params)
{
  std::lock_guard lock(count_mutex());
  instances->insert_or_assign(t, SortInstance{ constructor_id, params });
}

std::int32_t Yices2InstanceRef::get_instance_constructor(type_t t)
{
  std::lock_guard lock(count_mutex());
  auto it = instances->find(t);
  return it == instances->end() ? -1 : it->second.constructor_id;
}

std::vector<type_t> Yices2InstanceRef::get_instance_params(type_t t)
{
  std::lock_guard lock(count_mutex());
  return instances->at(t).params;
}

}  // namespace smt
