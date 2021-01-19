/*********************                                                        */
/*! \file generic_solver.h
** \verbatim
** Top contributors (to current version):
**   Yoni Zohar
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Represents a Generic Solver.
**
**/

#pragma once

#include <string>
#include <unordered_map>
#include <unordered_set>

#include "generic_sort.h"
#include "generic_term.h"
#include "solver.h"

namespace smt {

class GenericSolver : public AbsSmtSolver
{
 public:
  GenericSolver(std::string path,
                std::vector<std::string> cmd_line_args,
                uint write_buf_size = 256,
                uint read_buf_size = 256);
  ~GenericSolver();
  std::string to_smtlib_def(Term term) const;
  Sort make_sort(const std::string name, uint64_t arity) const override;
  Sort make_sort(const SortKind sk) const override;
  Sort make_sort(const SortKind sk, uint64_t size) const override;
  Sort make_sort(const SortKind sk, const Sort & sort1) const override;
  Sort make_sort(const SortKind sk,
                 const Sort & sort1,
                 const Sort & sort2) const override;
  Sort make_sort(const SortKind sk,
                 const Sort & sort1,
                 const Sort & sort2,
                 const Sort & sort3) const override;
  Sort make_sort(const Sort & sort_con, const SortVec & sorts) const override;

  Sort make_sort(const SortKind sk, const SortVec & sorts) const override;
  Sort make_sort(const DatatypeDecl & d) const override;

  DatatypeDecl make_datatype_decl(const std::string & s) override;
  DatatypeConstructorDecl make_datatype_constructor_decl(
      const std::string s) override;
  void add_constructor(DatatypeDecl & dt,
                       const DatatypeConstructorDecl & con) const override;
  void add_selector(DatatypeConstructorDecl & dt,
                    const std::string & name,
                    const Sort & s) const override;
  void add_selector_self(DatatypeConstructorDecl & dt,
                         const std::string & name) const override;
  Term get_constructor(const Sort & s, std::string name) const override;
  Term get_tester(const Sort & s, std::string name) const override;
  Term get_selector(const Sort & s,
                    std::string con,
                    std::string name) const override;

  Term make_term(bool b) const override;
  Term make_term(int64_t i, const Sort & sort) const override;
  Term make_term(const std::string val,
                 const Sort & sort,
                 uint64_t base = 10) const override;
  Term make_term(const Term & val, const Sort & sort) const override;
  Term make_symbol(const std::string name, const Sort & sort) override;
  Term make_param(const std::string name, const Sort & sort) override;
  Term make_term(const Op op, const Term & t) const override;
  Term make_term(const Op op, const Term & t0, const Term & t1) const override;
  Term make_term(const Op op,
                 const Term & t0,
                 const Term & t1,
                 const Term & t2) const override;
  Term make_term(const Op op, const TermVec & terms) const override;
  Term get_value(const Term & t) const override;
  UnorderedTermMap get_array_values(const Term & arr,
                                    Term & out_const_base) const override;
  void get_unsat_core(UnorderedTermSet & out) override;
  // Will probably remove this eventually
  // For now, need to clear the hash table
  void reset() override;

  void set_opt(const std::string option, const std::string value) override;
  void set_logic(const std::string logic) override;
  void assert_formula(const Term & t) override;
  Result check_sat() override;
  Result check_sat_assuming(const TermVec & assumptions) override;
  void push(uint64_t num = 1) override;
  void pop(uint64_t num = 1) override;
  void reset_assertions() override;

 protected:

  /******************
   * helper methods *
   *******************/

  // open a connection to the binary via a pipe
  void start_solver();
  // close the connection to the binary
  void close_solver();

  // internal function to read solver's response
  std::string read_internal() const;

  // internal function to write to the solver's process
  void write_internal(std::string str) const;

  // run a command with the binary
  std::string run_command(std::string cmd,
                          bool verify_success_flag = true) const;

  // verify that we got `success`
  void verify_success(std::string result) const;
  /***********
   * members *
   ***********/

  // path to the solver binary
  std::string path;

  // command line arguments for the binary
  std::vector<std::string> cmd_line_args;

  // variables used for running processes
  int inpipefd[2];
  int outpipefd[2];
  pid_t pid;
  int status;
  char * write_buf;
  char * read_buf;

  // buffer sizes
  uint write_buf_size;
  uint read_buf_size;

  // maps between sort name and actual sort and vice verse
  std::unique_ptr<std::unordered_map<std::string, Sort>> name_sort_map;
  std::unique_ptr<std::unordered_map<Sort, std::string>> sort_name_map;

  // internal counter for naming terms
  uint * term_counter;

  // maps between sort name and actual sort and vice verse
  std::unique_ptr<std::unordered_map<std::string, Term>> name_term_map;
  std::unique_ptr<std::unordered_map<Term, std::string>> term_name_map;
  // used to hash terms via their internal string representation
  std::hash<std::string> str_hash;

  // flag that states whether current command is done being executed
  bool is_done(int just_read, std::string result) const;
};

}  // namespace smt
