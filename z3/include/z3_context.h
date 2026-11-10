/*!
 * \file z3_context.h
 * \brief A Z3 context, with what the backend keeps about it.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * The backend emulates some features Z3's API lacks, and keeps what the
 * emulation needs with the context, which every solver, sort and term of
 * the context shares. For example, Z3's API has no sort constructors, so
 * each application is an uninterpreted Z3 sort of an internal name, and
 * the context records what it applies, which Z3 cannot report.
 */

#pragma once

#include <z3++.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace smt {

class Z3Context : public z3::context
{
 public:
  /** A param named `name` of sort `sort`: a fresh constant, recorded so
   *  that every term of it reports a param
   */
  z3::expr add_param(const std::string & name, const z3::sort & sort);
  /** Whether add_param made `term` */
  bool is_param(const z3::expr & term) const;
  /** The name add_param was given for `term` */
  std::string get_param_name(const z3::expr & term) const;
  /** The sort the sort constructor `name` applied to `params` stands for:
   *  an uninterpreted sort made the first time and given back after, so
   *  that its sorts can report what it applies
   */
  z3::sort add_instance(const std::string & name,
                        const std::vector<z3::sort> & params);
  /** Whether add_instance made `sort` */
  bool is_instance(const z3::sort & sort) const;
  /** The name of the sort constructor `sort` applies, or the name of `sort`
   *  if add_instance did not make it
   */
  std::string get_instance_name(const z3::sort & sort) const;
  /** The sorts `sort` applies its sort constructor to, or none if
   *  add_instance did not make it
   */
  std::vector<z3::sort> get_instance_params(const z3::sort & sort) const;
  /** Records that a datatype named `name` was declared */
  void add_datatype_name(const std::string & name);
  /** Whether add_datatype_name recorded `name` */
  bool has_datatype_name(const std::string & name) const;

 private:
  /** A param and the name it was made with, which Z3 does not keep */
  struct Param
  {
    z3::expr term;
    std::string name;
  };

  // the params by their term's id; each keeps its term alive, so that Z3
  // cannot give the id to another term
  std::unordered_map<unsigned, Param> param_info = {};

  /** What an instance of a sort constructor applies */
  struct SortInstance
  {
    std::string name;
    std::vector<z3::sort> params;
  };

  /** A sort constructor's name and the ids of the sorts it is applied to */
  using InstanceKey = std::pair<std::string, std::vector<unsigned>>;
  struct InstanceKeyHash
  {
    std::size_t operator()(const InstanceKey & key) const;
  };

  // the instances, both by what they apply and by their sort's id; they
  // are destroyed before the context they live in
  std::unordered_map<InstanceKey, z3::sort, InstanceKeyHash>
      uninterp_sort_cache = {};
  std::unordered_map<unsigned, SortInstance> uninterp_sort_info = {};
  std::uint64_t count = 0;
  // Z3 keys a datatype by its name, so declaring a second datatype of one
  // name replaces the first's constructors
  std::unordered_set<std::string> datatype_names = {};
};

}  // namespace smt
