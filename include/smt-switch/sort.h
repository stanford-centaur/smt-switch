/*!
 * \file sort.h
 * \brief Abstract interface for SMT sorts
 * \author Makai Mann
 * \author Clark Barrett
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_SORT_H
#define SMT_SWITCH_SORT_H

#ifndef SMT_SWITCH_INTERNAL
// IWYU pragma: private, include "smt-switch/smt.h"
#endif

#include <cstddef>
#include <cstdint>
#include <ostream>
#include <string>
#include <vector>

#include "smt-switch/smt_defs.h"

namespace smt {

/** The kinds of sorts */
enum class SortKind
{
  ARRAY,
  BOOL,
  BV,
  INT,
  REAL,
  STRING,
  FUNCTION,
  UNINTERPRETED,
  UNINTERPRETED_CONS,  // sort constructor
  DATATYPE,
  CONSTRUCTOR,
  SELECTOR,
  TESTER
};

std::string to_string(SortKind sk);

std::ostream & operator<<(std::ostream & output, SortKind sk);

/**
   Abstract base class for representing an SMT sort.
   It holds a kind enum and any necessary data for that particular sort.

   Sort objects should never be constructed directly, but instead provided
   by a Solver.
 */
class AbsSort
{
 public:
  virtual ~AbsSort() = default;
  virtual std::string to_string() const;
  virtual std::size_t hash() const = 0;
  virtual SortKind get_kind() const = 0;
  // An accessor that does not apply to the sort's kind, e.g. get_width of
  // an Int sort, throws IncorrectUsageException
  virtual std::uint64_t get_width() const = 0;
  virtual Sort get_indexsort() const = 0;
  virtual Sort get_elemsort() const = 0;
  virtual std::vector<Sort> get_domain_sorts() const = 0;
  virtual Sort get_codomain_sort() const = 0;
  virtual std::string get_uninterpreted_name() const = 0;
  virtual std::size_t get_arity() const = 0;
  /** Returns the sort constructor an uninterpreted sort was made by
   *  applying.
   *  Throws an IncorrectUsageException for any other sort.
   */
  virtual Sort get_uninterpreted_constructor() const = 0;
  virtual std::vector<Sort> get_uninterpreted_param_sorts() const = 0;
  virtual Datatype get_datatype() const = 0;
  virtual bool compare(const Sort & sort) const = 0;
  /** Solvers that treat multiple kinds of terms as booleans should override
   * this.
   */
  virtual bool is_boolean() const;
};

}  // namespace smt

#endif  // SMT_SWITCH_SORT_H
