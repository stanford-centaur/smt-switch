/*!
 * \file yices2_extensions.cpp
 * \brief Helper functions for certain operations in the Yices C API
 * \author Amalee Wilson
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/yices2_extensions.h"

#include <gmp.h>  // IWYU pragma: keep (required by yices.h)
#include <yices.h>

#include <memory>
#include <string>

#include "smt-switch/exceptions.h"

using namespace std;

namespace smt {

namespace {

struct YicesStringDeleter
{
  void operator()(char * s) const { yices_free_string(s); }
};

}  // namespace

void detail::Yices2ModelDeleter::operator()(model_t * model) const
{
  yices_free_model(model);
}

string detail::get_yices2_error()
{
  unique_ptr<char, YicesStringDeleter> reason(yices_error_string());
  string msg(reason.get());
  yices_clear_error();
  // Yices2 ends a few of its error messages with a newline.
  if (!msg.empty() && msg.back() == '\n')
  {
    msg.pop_back();
  }
  return msg;
}

void detail::throw_yices2_error()
{
  error_code_t code = yices_error_code();
  string msg = get_yices2_error();
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

string detail::get_yices2_string(char * s)
{
  unique_ptr<char, YicesStringDeleter> owned(s);
  if (!owned)
  {
    throw_yices2_error();
  }
  return owned.get();
}

term_t ext_yices_select(term_t arr, term_t idx)
{
  term_t selection = yices_application1(arr, idx);
  return selection;
}

term_t ext_yices_store(term_t arr, term_t idx, term_t nu)
{
  term_t updated = yices_update1(arr, idx, nu);
  return updated;
}

term_t ext_yices_bvcomp(term_t t0, term_t t1)
{
  // ite(t0 == t1, #b1, #b0)
  return yices_ite(
      yices_eq(t0, t1), yices_bvconst_int64(1, 1), yices_bvconst_int64(1, 0));
}

term_t ext_yices_bvxor3(term_t t0, term_t t1, term_t t2)
{
  return yices_bvxor3(t0, t1, t2);
}

}  // namespace smt
