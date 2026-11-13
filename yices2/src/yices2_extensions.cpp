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

string detail::get_yices2_string(char * s)
{
  unique_ptr<char, YicesStringDeleter> owned(s);
  if (!owned)
  {
    throw SolverException(get_yices2_error());
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
