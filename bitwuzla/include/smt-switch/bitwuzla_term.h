/*!
 * \file bitwuzla_term.h
 * \brief Bitwuzla implementation of AbsTerm
 * \author Makai Mann
 * \author Samantha Archer
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_BITWUZLA_TERM_H
#define SMT_SWITCH_BITWUZLA_TERM_H

#include <bitwuzla/cpp/bitwuzla.h>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "smt-switch/bitwuzla_term_manager.h"
#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/term.h"

namespace smt {

class BzlaTerm : public AbsTerm
{
 public:
  BzlaTerm(const std::shared_ptr<BzlaTermManager> & manager, bitwuzla::Term n);
  /** The application of op to children
   *  @throws NotImplementedException for an operator Bitwuzla does not support
   *  @throws bitwuzla::Exception where Bitwuzla rejects the application
   */
  BzlaTerm(const std::shared_ptr<BzlaTermManager> & manager,
           const Op & op,
           const std::vector<bitwuzla::Term> & children);
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
  std::string get_constructor_name() const override;
  std::string get_param_name() const override;
  std::string get_selector_name() const override;
  std::string get_symbol_name() const override;
  std::uint64_t to_int() const override;
  std::int64_t to_signed_int() const override;
  std::string to_bits() const override;
  bool to_bool() const override;
  std::string print_value_as(SortKind sk) const override;

  // Getters for solver-specific objects
  // for interacting with third-party Bitwuzla-specific software

  const bitwuzla::Term get_bitwuzla_term() const;

 protected:
  std::size_t get_num_children() const override;
  Term get_child(std::size_t i) const override;

  // the term manager that owns term, kept alive for as long as term is
  // (declared first, so that term is destroyed before it)
  const std::shared_ptr<BzlaTermManager> tm;
  // the actual API level node that is used
  const bitwuzla::Term term;

  friend class BzlaSolver;
  friend class BzlaInterpolator;
};

}  // namespace smt

#endif  // SMT_SWITCH_BITWUZLA_TERM_H
