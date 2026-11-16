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
#include <vector>

#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

namespace smt {
class Cvc5Term : public AbsTerm
{
 public:
  explicit Cvc5Term(cvc5::Term t);
  /** The application of op to children, made by tm
   *  @throws IncorrectUsageException for an operator cvc5 does not support
   *  @throws cvc5::CVC5ApiException where cvc5 rejects the application
   */
  Cvc5Term(cvc5::TermManager & tm,
           const Op & op,
           const std::vector<cvc5::Term> & children);
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
  std::string to_bits() const override;
  bool to_bool() const override;
  std::string print_value_as(SortKind sk) const override;

  // Getters for solver-specific objects
  // for interacting with third-party cvc5-specific software
  cvc5::Term get_cvc5_term() const;

 protected:
  std::size_t get_num_children() const override;
  Term get_child(std::size_t i) const override;

  cvc5::Term term;

  friend class Cvc5Solver;
  friend class Cvc5Interpolator;
};

}  // namespace smt

#endif  // SMT_SWITCH_CVC5_TERM_H
