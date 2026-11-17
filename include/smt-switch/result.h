/*!
 * \file result.h
 * \brief The result of a call to check-sat or check-sat-assuming
 * \author Makai Mann
 * \author Clark Barrett
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_RESULT_H
#define SMT_SWITCH_RESULT_H

#ifndef SMT_SWITCH_INTERNAL
// IWYU pragma: private, include "smt-switch/smt.h"
#endif

#include <ostream>
#include <string>

namespace smt {

class Result
{
 public:
  /** A null result, as no check has made it */
  Result() = default;
  /** A satisfiable result */
  static Result sat();
  /** An unsatisfiable result */
  static Result unsat();
  /** An unknown result, for the reason the explanation gives */
  static Result unknown(std::string explanation = "no explanation");

  bool is_sat() const;
  bool is_unsat() const;
  bool is_unknown() const;
  bool is_null() const;
  /** @throws IncorrectUsageException if the result is not unknown */
  std::string get_explanation() const;
  std::string to_string() const;

  /** Whether both results are of the same kind, whatever their explanations
   */
  friend bool operator==(const Result & r1, const Result & r2);

 private:
  enum class Kind
  {
    Null,
    Sat,
    Unsat,
    Unknown
  };

  Result(Kind kind, std::string explanation);

  Kind kind_ = Kind::Null;
  std::string explanation_ = "null";
};

std::ostream & operator<<(std::ostream & output, const Result r);
bool operator!=(const Result & r1, const Result & r2);

}  // namespace smt

#endif  // SMT_SWITCH_RESULT_H
