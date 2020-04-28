#pragma once

#include "solver.h"

#include <unordered_map>

namespace smt {

/**
 *  Solver class that creates an API trace that can dumped to a C++ file
 */
class ApiTraceSolver : public AbsSmtSolver
{
 public:
  ApiTraceSolver(SmtSolver s) : sub_solver(s)
  {
    trace_lines = new std::vector<std::string>();
    term2name = new std::unordered_map<std::uintptr_t, std::string>();
    sort2name = new std::unordered_map<std::uintptr_t, std::string>();
    nid = new uint64_t;
    *nid = 0;
    sid = new uint64_t;
    *sid = 0;
    rid = new uint64_t;
    *rid = 0;

    trace_lines->push_back("/* instantiate SmtSolver with name s here */");
  }
  ~ApiTraceSolver()
  {
    delete trace_lines;
    delete term2name;
    delete nid;
    delete rid;
  }

  void set_opt(const std::string option, const std::string value) override;
  void set_logic(const std::string logic) override;
  void assert_formula(const Term & t) override;
  Result check_sat() override;
  Result check_sat_assuming(const TermVec & assumptions) override;
  void push(uint64_t num = 1) override;
  void pop(uint64_t num = 1) override;
  Term get_value(Term & t) const override;
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
  // helper methods for making a term with a primitive op
  Term apply_prim_op(PrimOp op, Term t) const;
  Term apply_prim_op(PrimOp op, Term t0, Term t1) const;
  Term apply_prim_op(PrimOp op, Term t0, Term t1, Term t2) const;
  Term apply_prim_op(PrimOp op, TermVec terms) const;
  void dump_smt2(std::string filename) const override;
  void dump_api_trace(std::string filename) const;

 protected:
  std::vector<std::string> * trace_lines;
  // yes, I'm hashing on pointers
  // this is important, because the stored names for terms should not
  // correspond to the actual term values
  // e.g. two terms might be equal in one run of the solver but not
  // when replayed with a different solver
  std::unordered_map<std::uintptr_t, std::string> * term2name;
  std::unordered_map<std::uintptr_t, std::string> * sort2name;
  uint64_t * nid;
  uint64_t * sid;
  uint64_t * rid;
  SmtSolver sub_solver;
};

}  // namespace smt
