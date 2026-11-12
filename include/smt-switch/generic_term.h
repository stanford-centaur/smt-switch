/*!
 * \file generic_term.h
 * \brief Class that represents a term with Op and children
 * \author Yoni Zohar
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_GENERIC_TERM_H
#define SMT_SWITCH_GENERIC_TERM_H

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>

#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

namespace smt {

class GenericTerm : public AbsTerm
{
 public:
  // General constructor
  // throws IncorrectUsageException if there is neither an op nor a repr
  GenericTerm(Sort s, Op o, TermVec c, std::string r);
  // this one is for making symbols
  // if passed with true, sets is_sym true
  // otherwise sets is_param true
  // only symbols and parameters have names
  // symbols are "free" uninterpreted constants and functions
  // params are bound variables
  GenericTerm(Sort s, Op o, TermVec c, std::string r, bool symbol);

  /** Returns true iff the term AND sort are equivalent
   *  @param t the term to compare with (assumed to be GenericTerm)
   *  @return true iff the term and sort match t
   */
  bool compare(const Term & t) const override;
  Op get_op() const override;
  Sort get_sort() const override;
  std::size_t get_id() const override;
  std::string to_string() const override;
  std::size_t hash() const override;
  bool is_value() const override;
  std::string get_constructor_name() const override;
  std::string get_param_name() const override;
  std::string get_selector_name() const override;
  std::string get_symbol_name() const override;
  std::uint64_t to_int() const override;
  std::int64_t to_signed_int() const override;
  std::string print_value_as(SortKind sk) const override;
  // is this a ground term
  bool is_ground() const;
  bool is_symbol() const override;
  bool is_param() const override;
  bool is_symbolic_const() const override;
  TermVec get_children() const;

 protected:
  std::size_t get_num_children() const override;
  Term get_child(std::size_t i) const override;

  std::string compute_string() const;

  /** check whether this is a ground term
   * (does not have free variables)
   * Should only be called from the constructor.
   */
  bool compute_ground();

  // true iff this is a ground term
  bool ground = false;

  /**
   * A hash function for strings,
   * to be used to compute the hash of the term.
   */
  std::hash<std::string> str_hash = {};

  // The term's sort
  Sort sort;

  /**
   * The top-most operator of the term.
   * null op if there isn't any op.
   */
  Op op;

  // Immediate children of the term, null for a leaf
  std::shared_ptr<const TermVec> children;

  // A string representation of the term
  mutable std::string repr;

  // is this a symbolic constant
  bool is_sym = false;

  // is this a variable
  bool is_par = false;

  // So GenericSolver can access protected members:
  friend class GenericSolver;
};

}  // namespace smt

#endif  // SMT_SWITCH_GENERIC_TERM_H
