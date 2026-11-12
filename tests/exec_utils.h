/*!
 * \file exec_utils.h
 * \brief Convenience functions for testing
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_EXEC_UTILS_H
#define SMT_SWITCH_EXEC_UTILS_H

#include <sstream>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

namespace smt_tests {
void dump_and_run(std::string_view executable_path,
                  std::stringbuf & strbuf,
                  std::vector<std::unordered_set<std::string>> expected_results,
                  std::string extra_opts = "");
}  // namespace smt_tests

#endif  // SMT_SWITCH_EXEC_UTILS_H
