/*!
 * \file cvc5_term.h
 * \brief cvc5 implementation of AbsTerm
 * \author Makai Mann
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_CVC5_TERM_H
#define SMT_SWITCH_CVC5_TERM_H

#include <cvc5/cvc5.h>

#include <cstddef>
#include <cstdint>
#include <string>

#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

namespace smt {
class Cvc5Term : public AbsTerm
{
 public:
  explicit Cvc5Term(cvc5::Term t);
  std::size_t hash() const override;
  std::size_t get_id() const override;
  bool compare(const Term & absterm) const override;
  Op get_op() const override;
  Sort get_sort() const override;
  bool is_symbol() const override;
  bool is_param() const override;
  bool is_symbolic_const() const override;
  bool is_value() const override;
  virtual std::string to_string() const override;
  virtual std::wstring getStringValue() const override;
  std::string get_constructor_name() const override;
  std::string get_param_name() const override;
  std::string get_selector_name() const override;
  std::string get_symbol_name() const override;
  uint64_t to_int() const override;
  int64_t to_signed_int() const override;
  bool to_bool() const override;
  std::string print_value_as(SortKind sk) const override;

  // Getters for solver-specific objects
  // for interacting with third-party cvc5-specific software
  ::cvc5::Term get_cvc5_term() const;

 protected:
  std::size_t get_num_children() const override;
  Term get_child(std::size_t i) const override;

  cvc5::Term term;

  friend class Cvc5Solver;
  friend class Cvc5Interpolator;
};

/** The cvc5 kind of the applications of po
 *  @throws IncorrectUsageException for NUM_OPS_AND_NULL or an out-of-range
 *          value
 */
cvc5::Kind to_cvc5_kind(PrimOp po);

/** The PrimOp of the applications of kind
 *  @throws NotImplementedException for a kind that no PrimOp stands for
 */
PrimOp to_primop(cvc5::Kind kind);

}  // namespace smt

#endif  // SMT_SWITCH_CVC5_TERM_H
