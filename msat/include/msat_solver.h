#ifndef SMT_MSAT_SOLVER_H
#define SMT_MSAT_SOLVER_H

#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "msat_sort.h"
#include "msat_term.h"

#include "mathsat.h"

#include "exceptions.h"
#include "ops.h"
#include "result.h"
#include "smt.h"
#include "sort.h"
#include "term.h"

namespace smt {
/**
   Msat Solver
 */
class MsatSolver : public AbsSmtSolver
{
 public:
  MsatSolver()
  {
    cfg = msat_create_config();
    env = msat_create_env(cfg);
  };
  MsatSolver(const MsatSolver &) = delete;
  MsatSolver & operator=(const MsatSolver &) = delete;
  ~MsatSolver(){};
  void set_opt(const std::string option, bool value) const override;
  void set_opt(const std::string option,
               const std::string value) const override;
  void set_logic(const std::string logic) const override;
  void assert_formula(const Term & t) const override;
  Result check_sat() const override;
  Result check_sat_assuming(const TermVec & assumptions) const override;
  void push(unsigned int num = 1) const override;
  void pop(unsigned int num = 1) const override;
  Term get_value(Term & t) const override;
  Sort make_sort(const std::string name, unsigned int arity) const override;
  Sort make_sort(SortKind sk) const override;
  Sort make_sort(SortKind sk, unsigned int size) const override;
  Sort make_sort(SortKind sk,
                 const Sort & idxsort,
                 const Sort & elemsort) const override;
  Sort make_sort(SortKind sk,
                 const std::vector<Sort> & sorts,
                 const Sort & sort) const override;
  Term make_value(bool b) const override;
  Term make_value(unsigned int i, const Sort & sort) const override;
  Term make_value(const std::string val,
                  const Sort & sort,
                  unsigned int base = 10) const override;
  Term make_value(const Term & val, const Sort & sort) const override;
  Term make_term(const std::string s, const Sort & sort) override;
  /* build a new term */
  Term make_term(Op op, const Term & t) const override;
  Term make_term(Op op, const Term & t0, const Term & t1) const override;
  Term make_term(Op op,
                 const Term & t0,
                 const Term & t1,
                 const Term & t2) const override;
  Term make_term(Op op, const std::vector<Term> & terms) const override;
  void reset() override;
  void reset_assertions() override;
  bool has_symbol(const std::string name) const override;
  Term lookup_symbol(const std::string name) const override;
  void dump_smt2(FILE * file) const override;

 protected:
  msat_config cfg;
  msat_env env;
  // TODO: possibly remove this
  // keep track of created symbols for has_symbol and lookup_symbol
  // std::unordered_map<std::string, Term> symbols;
};
}  // namespace smt

#endif
