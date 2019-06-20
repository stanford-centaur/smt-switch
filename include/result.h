#ifndef SMT_RESULT_H
#define SMT_RESULT_H

namespace smt
{
  enum ResultType
  {
   SAT=0,
   UNSAT,
   UNKNOWN
  };

  struct Result
  {
    Result(ResultType rt, std::string explanation="")
      : result(rt), explanation(explanation) {}
    bool is_sat() { return result == SAT; };
    bool is_unsat() { return result == UNSAT; };
    bool is_unknown() { return result == UNKNOWN; };
    ResultType result;
    std::string explanation;
  };
}

#endif
