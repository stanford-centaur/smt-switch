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
  // constructor does basically nothing
  // but in mathsat factory, MUST setup_env
  // this is done after constructing because need to call
  // the virtual function -- e.g. simulating dynamic binding
  MsatSolver() : logic(""){};
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
  void set_logic(const std::string log) override;
  void assert_formula(const Term & t) override;
  Result check_sat() override;
  Result check_sat_assuming(const TermVec & assumptions) override;
  void push(uint64_t num = 1) override;
  void pop(uint64_t num = 1) override;
  Term get_value(const Term & t) const override;
  UnorderedTermMap get_array_values(const Term & arr,
                                    Term & out_const_base) const override;
  TermVec get_unsat_core() override;
  Sort make_sort(const std::string name, uint64_t arity) const override;
  Sort make_sort(SortKind sk) const override;
  Sort make_sort(SortKind sk, uint64_t size) const override;
  Sort make_sort(SortKind sk, const Sort & sort1) const override;
  Sort make_sort(SortKind sk,
                 const Sort & sort1,
                 const Sort & sort2) const override;
  Sort make_sort(SortKind sk,
                 const Sort & sort1,
                 const Sort & sort2,
                 const Sort & sort3) const override;
  Sort make_sort(SortKind sk, const SortVec & sorts) const override;
  Term make_term(bool b) const override;
  Term make_term(int64_t i, const Sort & sort) const override;
  Term make_term(const std::string val,
                 const Sort & sort,
                 uint64_t base = 10) const override;
  Term make_term(const Term & val, const Sort & sort) const override;
  Term make_symbol(const std::string name, const Sort & sort) override;
  /* build a new term */
  Term make_term(Op op, const Term & t) const override;
  Term make_term(Op op, const Term & t0, const Term & t1) const override;
  Term make_term(Op op,
                 const Term & t0,
                 const Term & t1,
                 const Term & t2) const override;
  Term make_term(Op op, const TermVec & terms) const override;
  void reset() override;
  void reset_assertions() override;
  Term substitute(const Term term,
                  const UnorderedTermMap & substitution_map) const override;

  void dump_smt2(std::string filename) const override;

 protected:
  msat_config cfg;
  msat_env env;
  bool valid_model;
  std::string logic;

  // helper function for creating labels for assumptions
  msat_term label(msat_term p) const;
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
  void assert_formula(const Term & t) override;
  Result check_sat() override;
  Result check_sat_assuming(const TermVec & assumptions) override;
  Term get_value(const Term & t) const override;
  bool get_interpolant(const Term & A,
                       const Term & B,
                       Term & out_I) const override;
};

}  // namespace smt

#endif
