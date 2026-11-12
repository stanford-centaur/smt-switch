/*!
 * \file bitwuzla_term_manager.h
 * \brief A Bitwuzla term manager, with what the backend keeps about it
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * The backend emulates some features Bitwuzla's API lacks, and keeps what
 * the emulation needs with the term manager, which every sort and term of
 * the term manager shares. For example, Bitwuzla's API has no sort
 * constructors, so each application is an uninterpreted Bitwuzla sort named
 * as the applied sort prints, and the term manager records what it
 * applies, which Bitwuzla cannot report.
 */
#ifndef SMT_SWITCH_BITWUZLA_TERM_MANAGER_H
#define SMT_SWITCH_BITWUZLA_TERM_MANAGER_H

#include <bitwuzla/cpp/bitwuzla.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

namespace smt {

class BzlaTermManager : public bitwuzla::TermManager
{
 public:
  /** Records a new sort constructor of `name` and `arity`, distinct from
   *  every other even of the same name, as Bitwuzla's declared sorts are
   *  @return the constructor's id
   */
  std::uint64_t add_constructor(const std::string & name, std::uint64_t arity);
  /** The name of the sort constructor add_constructor recorded as `id` */
  std::string get_constructor_name(std::uint64_t id) const;
  /** The arity of the sort constructor add_constructor recorded as `id` */
  std::uint64_t get_constructor_arity(std::uint64_t id) const;
  /** The sort the sort constructor `constructor` applied to `params` stands
   *  for: an uninterpreted sort named `symbol`, made the first time and
   *  given back after, so that its sorts can report what it applies
   */
  bitwuzla::Sort add_instance(std::uint64_t constructor,
                              const std::vector<bitwuzla::Sort> & params,
                              const std::string & symbol);
  /** Whether add_instance made `sort` */
  bool is_instance(const bitwuzla::Sort & sort) const;
  /** The id of the sort constructor `sort` applies, which add_instance
   *  made
   */
  std::uint64_t get_instance_constructor(const bitwuzla::Sort & sort) const;
  /** The name of the sort constructor `sort` applies, or the symbol of
   *  `sort` if add_instance did not make it
   */
  std::string get_instance_name(const bitwuzla::Sort & sort) const;
  /** The sorts `sort` applies its sort constructor to, or none if
   *  add_instance did not make it
   */
  std::vector<bitwuzla::Sort> get_instance_params(
      const bitwuzla::Sort & sort) const;

 private:
  /** A sort constructor's name and arity */
  struct SortConstructor
  {
    std::string name;
    std::uint64_t arity;
  };

  /** What an instance of a sort constructor applies */
  struct SortInstance
  {
    std::uint64_t constructor;
    std::vector<bitwuzla::Sort> params;
  };

  /** A sort constructor's id and the ids of the sorts it is applied to */
  using InstanceKey = std::pair<std::uint64_t, std::vector<std::uint64_t>>;
  struct InstanceKeyHash
  {
    std::size_t operator()(const InstanceKey & key) const;
  };

  // the constructors, by id
  std::vector<SortConstructor> constructors = {};
  // the instances, both by what they apply and by their sort's id; they
  // are destroyed before the term manager they live in
  std::unordered_map<InstanceKey, bitwuzla::Sort, InstanceKeyHash>
      uninterp_sort_cache = {};
  std::unordered_map<std::uint64_t, SortInstance> uninterp_sort_info = {};
};

}  // namespace smt

#endif  // SMT_SWITCH_BITWUZLA_TERM_MANAGER_H
