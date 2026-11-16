/*!
 * \file yices2_instance_ref.cpp
 * \brief Counts the references to the Yices instance, setting it up for the
 *        first and freeing it after the last
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/yices2_instance_ref.h"

#include <gmp.h>  // IWYU pragma: keep (required by yices.h)
#include <yices.h>

#include <cstddef>
#include <cstdint>
#include <mutex>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "smt-switch/exceptions.h"

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
// instances, and the constant arrays' bound variables, also under
// count_mutex, made and freed with the instance
std::unordered_set<term_t> * functions = nullptr;
std::unordered_map<std::int32_t, SortConstructor> * constructors = nullptr;
std::unordered_map<type_t, SortInstance> * instances = nullptr;
std::unordered_map<type_t, term_t> * index_variables = nullptr;

void acquire()
{
  std::lock_guard lock(count_mutex());
  if (count++ == 0)
  {
    yices_init();
    functions = new std::unordered_set<term_t>;
    constructors = new std::unordered_map<std::int32_t, SortConstructor>;
    instances = new std::unordered_map<type_t, SortInstance>;
    index_variables = new std::unordered_map<type_t, term_t>;
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
    delete index_variables;
    index_variables = nullptr;
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

term_t Yices2InstanceRef::get_index_variable(type_t index_type)
{
  std::lock_guard lock(count_mutex());
  auto it = index_variables->find(index_type);
  if (it != index_variables->end())
  {
    return it->second;
  }
  term_t variable = yices_new_variable(index_type);
  index_variables->emplace(index_type, variable);
  return variable;
}

void Yices2InstanceRef::throw_error()
{
  error_code_t code = yices_error_code();
  char * reason = yices_error_string();
  std::string msg(reason);
  yices_free_string(reason);
  yices_clear_error();
  // Yices2 ends a few of its error messages with a newline.
  if (!msg.empty() && msg.back() == '\n')
  {
    msg.pop_back();
  }
  // Yices reports most refusals under codes of their own, so only those
  // that are not the caller's mistake are listed.
  switch (code)
  {
    case CTX_LOGIC_NOT_SUPPORTED:
    case CTX_UF_NOT_SUPPORTED:
    case CTX_ARITH_NOT_SUPPORTED:
    case CTX_BV_NOT_SUPPORTED:
    case CTX_ARRAYS_NOT_SUPPORTED:
    case CTX_QUANTIFIERS_NOT_SUPPORTED:
    case CTX_LAMBDAS_NOT_SUPPORTED:
    case CTX_NONLINEAR_ARITH_NOT_SUPPORTED:
    case CTX_FORMULA_NOT_IDL:
    case CTX_FORMULA_NOT_RDL:
    case CTX_SCALAR_NOT_SUPPORTED:
    case CTX_TUPLE_NOT_SUPPORTED:
    case CTX_UTYPE_NOT_SUPPORTED:
    case CTX_HIGH_ORDER_FUN_NOT_SUPPORTED:
    case CTX_OPERATION_NOT_SUPPORTED:
    case CTX_UNKNOWN_DELEGATE:
    case CTX_DELEGATE_NOT_AVAILABLE:
    case CTX_UNKNOWN_PARAMETER:
    case EVAL_NOT_SUPPORTED:
    case YVAL_NOT_SUPPORTED:
    case MDL_GEN_TYPE_NOT_SUPPORTED:
    case MDL_GEN_NONLINEAR:
    case MDL_GEN_UNSUPPORTED_TERM:
    case MCSAT_ERROR_UNSUPPORTED_THEORY:
    case MCSAT_ERROR_ASSUMPTION_TERM_NOT_SUPPORTED:
      throw NotImplementedException(msg);
    case DEGREE_OVERFLOW:
    case CTX_TOO_MANY_ARITH_VARS:
    case CTX_TOO_MANY_ARITH_ATOMS:
    case CTX_TOO_MANY_BV_VARS:
    case CTX_TOO_MANY_BV_ATOMS:
    case CTX_ARITH_SOLVER_EXCEPTION:
    case CTX_BV_SOLVER_EXCEPTION:
    case CTX_ARRAY_SOLVER_EXCEPTION:
    case CTX_EF_INTERNAL_ERROR:
    case EVAL_OVERFLOW:
    case EVAL_FAILED:
    case EVAL_CONVERSION_FAILED:
    case MDL_CONSTRUCTION_FAILED:
    case YVAL_OVERFLOW:
    case MDL_GEN_FAILED:
    case INTERNAL_EXCEPTION: throw SolverException(msg);
    case OUTPUT_ERROR: throw SystemException(msg);
    case YICES_NO_ERROR:
    case BAD_TERM_DECREF:
    case BAD_TYPE_DECREF: throw InternalException(msg);
    default: throw IncorrectUsageException(msg);
  }
}

}  // namespace smt
