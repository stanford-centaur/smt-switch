/*!
 * \file yices2_instance_ref.h
 * \brief A reference to the Yices instance, which lives while any is held.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Yices keeps its terms, types, contexts and configurations in one global
 * instance per process, set up by yices_init() and freed by yices_exit(). A
 * term or sort can outlive the solver that made it, so every Yices2Solver,
 * Yices2Sort and Yices2Term holds a Yices2InstanceRef: the first one made
 * calls yices_init(), and the last one destroyed calls yices_exit().
 *
 * It also records which symbols are functions. Yices has no array type, so
 * an array is a function to it, and a term cannot say which one it is.
 */

#pragma once

#include <gmp.h>  // IWYU pragma: keep (required by yices.h)
#include <yices.h>

namespace smt {

class Yices2InstanceRef
{
 public:
  Yices2InstanceRef();
  Yices2InstanceRef(const Yices2InstanceRef & other);
  // each object is already counted, so assigning changes nothing
  Yices2InstanceRef & operator=(const Yices2InstanceRef & other) = default;
  ~Yices2InstanceRef();

  /** Records that the symbol `t` was declared with a function sort. The
   * record lasts as long as the Yices instance, as term ids do.
   */
  static void mark_function(term_t t);
  /** Whether `t` is a symbol mark_function recorded */
  static bool is_function(term_t t);
};

}  // namespace smt
