/*!
 * \file msat_env.h
 * \brief A MathSAT environment, with what the backend keeps about it.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * The backend emulates some features MathSAT's API lacks, and keeps what the
 * emulation needs with the environment, which every sort and term of the
 * environment shares. For example, MathSAT's API has no sort constructors,
 * so each application is an uninterpreted MathSAT type of an internal name,
 * and the environment records what it applies, which MathSAT cannot report.
 */
#ifndef SMT_SWITCH_MSAT_ENV_H
#define SMT_SWITCH_MSAT_ENV_H

#include <mathsat.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

namespace smt {

class MsatEnv : public msat_env
{
 public:
  /** Takes ownership of `env` and of `config`, the configuration it was
   *  made from
   */
  MsatEnv(msat_env env, msat_config config);
  MsatEnv(const MsatEnv &) = delete;
  MsatEnv & operator=(const MsatEnv &) = delete;
  /** Destroys the environment and then its configuration, as MathSAT
   *  forbids destroying a configuration an environment still uses
   */
  ~MsatEnv();

  /** The type the sort constructor `name` applied to `params` stands for:
   *  an uninterpreted type made the first time and given back after, so
   *  that its sorts can report what it applies
   */
  msat_type add_instance(const std::string & name,
                         const std::vector<msat_type> & params);
  /** Whether add_instance made `t` */
  bool is_instance(msat_type t) const;
  /** The name of the sort constructor `t` applies, or MathSAT's
   *  representation of `t` if add_instance did not make it
   */
  std::string get_instance_name(msat_type t) const;
  /** The types `t` applies its sort constructor to, or none if
   *  add_instance did not make it
   */
  std::vector<msat_type> get_instance_params(msat_type t) const;

 private:
  /** What an instance of a sort constructor applies */
  struct SortInstance
  {
    std::string name;
    std::vector<msat_type> params;
  };

  /** A sort constructor's name and the ids of the types it is applied to */
  using InstanceKey = std::pair<std::string, std::vector<std::size_t>>;
  struct InstanceKeyHash
  {
    std::size_t operator()(const InstanceKey & key) const;
  };

  msat_config cfg;

  // the instances, both by what they apply and by their type's id
  std::unordered_map<InstanceKey, msat_type, InstanceKeyHash>
      uninterp_sort_cache = {};
  std::unordered_map<std::size_t, SortInstance> uninterp_sort_info = {};
  std::uint64_t count = 0;
};

}  // namespace smt

#endif  // SMT_SWITCH_MSAT_ENV_H
