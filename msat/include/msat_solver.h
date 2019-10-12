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
  // constructor does nothing
  // but in mathsat factory, MUST setup_env
  // this is done after constructing because need to call
  // the virtual function -- e.g. simulating dynamic binding
  MsatSolver(){};
  MsatSolver(const MsatSolver &) = delete;
  MsatSolver & operator=(const MsatSolver &) = delete;
  ~MsatSolver()
  {
    // Note: even with this, mathsat leaks
    // a program that just creates a msat_env leaks
    //  -- be careful, valgrind won't report leaks on statically compiled
    //  binaries
    msat_destroy_env(env);
    msat_destroy_config(cfg);
  }
  virtual void setup_env()
  {
    cfg = msat_create_config();
    msat_set_option(cfg, "model_generation", "true");
    env = msat_create_env(cfg);
    valid_model = false;
  }
  void set_opt(const std::string option, const std::string value) override;
  void set_logic(const std::string logic) const override;
  void assert_formula(const Term & t) const override;
  Result check_sat() override;
  Result check_sat_assuming(const TermVec & assumptions) override;
  void push(unsigned int num = 1) override;
  void pop(unsigned int num = 1) override;
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
  Term substitute(const Term term,
                  const UnorderedTermMap & substitution_map) const override;

  void dump_smt2(FILE * file) const override;

 protected:
  msat_config cfg;
  msat_env env;
  bool valid_model;

};

// Interpolating Solver
class MsatInterpolatingSolver : public MsatSolver
{
 public:
  MsatInterpolatingSolver() {}
  MsatInterpolatingSolver(const MsatInterpolatingSolver &) = delete;
  MsatInterpolatingSolver & operator=(const MsatInterpolatingSolver &) = delete;
  ~MsatInterpolatingSolver() {}
  virtual void setup_env() override
  {
    cfg = msat_create_config();
    msat_set_option(cfg, "theory.bv.eager", "false");
    msat_set_option(cfg, "theory.bv.bit_blast_mode", "0");
    msat_set_option(cfg, "interpolation", "true");
    // TODO: decide if we should add this
    // msat_set_option(cfg, "theory.eq_propagation", "false");
    env = msat_create_env(cfg);
    valid_model = false;
  }
  void set_opt(const std::string option, const std::string value) override;
  void assert_formula(const Term & t) const override;
  Result check_sat() override;
  Result check_sat_assuming(const TermVec & assumptions) override;
  Term get_value(Term & t) const override;
  bool get_interpolant(const Term & A,
                       const Term & B,
                       Term & out_I) const override;
};

}  // namespace smt

#endif
