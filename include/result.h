#ifndef SMT_RESULT_H
#define SMT_RESULT_H

namespace smt
{
enum ResultType
{
  SAT = 0,
  UNSAT,
  UNKNOWN,
  /** IMPORTANT: This must stay at the bottom.
      It's only use is for sizing the result2str array
  */
  NUM_RESULTS
};

struct Result
{
  Result() : result(NUM_RESULTS), explanation("null") {}
  Result(ResultType rt, std::string explanation = "")
      : result(rt), explanation(explanation)
  {
  }
  bool is_sat() { return result == SAT; };
  bool is_unsat() { return result == UNSAT; };
  bool is_unknown() { return result == UNKNOWN; };
  bool is_null() { return result == NUM_RESULTS; };
  std::string to_string() const;
  ResultType result;
  std::string explanation;
  };

  std::ostream & operator<<(std::ostream & output, const Result r);
}

#endif
