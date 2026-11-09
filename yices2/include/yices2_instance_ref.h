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
 * an array is a function to it, and a term cannot say which one it is. And
 * it records the sort constructors and their instances, as Yices reports
 * neither a constructor's name and arity nor what an instance applies.
 */

#pragma once

#include <yices_types.h>

#include <cstdint>
#include <string>
#include <vector>

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

  /** Records the name and arity of a sort constructor, by the macro id
   * yices_type_constructor gave it, which Yices cannot report back
   */
  static void add_constructor(std::int32_t id,
                              const std::string & name,
                              std::uint32_t arity);
  /** The name of a sort constructor add_constructor recorded */
  static std::string get_constructor_name(std::int32_t id);
  /** The arity of a sort constructor add_constructor recorded */
  static std::uint32_t get_constructor_arity(std::int32_t id);
  /** Records that the type `t` is a sort constructor applied to `params`,
   * which Yices cannot report back
   */
  static void add_instance(type_t t,
                           std::int32_t constructor_id,
                           const std::vector<type_t> & params);
  /** The macro id of the sort constructor the type `t` applies, or -1 if
   * add_instance recorded none
   */
  static std::int32_t get_instance_constructor(type_t t);
  /** What add_instance recorded `t` to apply its constructor to */
  static std::vector<type_t> get_instance_params(type_t t);
};

}  // namespace smt
