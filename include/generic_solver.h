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
** The current implementation of the generic solver has the following
** limitations:
** 1. Some AbsSmtSolver methods are not implemented.
**    These functions are defined first, under an appropriate comment below.
** 2. The buffer size used to communicate with the binary of the solver
**    is limited to values between 2 and 256.
** 3. Generic solvers cannot be used in term transfer/translation.
** 4. This feature is currently linux only -- no support for macOS.
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

  /***************************************************************/
  /* methods from AbsSmtSolver that are currently not implemented*/
  /***************************************************************/
  UnorderedTermMap get_array_values(const Term & arr,
                                    Term & out_const_base) const override;
  Sort make_sort(const Sort & sort_con, const SortVec & sorts) const override;
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

  /***************************************************************/
  /* methods from AbsSmtSolver that are implemented              */
  /***************************************************************/
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

  Sort make_sort(const SortKind sk, const SortVec & sorts) const override;

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

  /** Helper functions for the corresponding make_term
   * functions with the same arguments.
   * Also used to parse get_value responses.
   */
  Term make_value(bool b) const;
  Term make_value(int64_t i, const Sort & sort) const;
  Term make_value(const std::string val,
                  const Sort & sort,
                  uint64_t base = 10) const;

  // returns a string representation of a term in smtlib
  std::string to_smtlib_def(Term term) const;

  // when an SMT-LIB compliant solver is supposed
  // to return a result (e.g., get-value),
  // a result that starts with "(error " indicates
  // that an error occurred.
  // This cannot be caught by print-success,
  // which is not utilized for commands that
  // expect a result.
  void check_no_error(std::string str) const;

  // parse solver's response from get-sat-assumptions
  UnorderedTermSet get_assumptions_from_string(std::string result) const;

  // create an smt-lib constant array value.
  // used for make_term
  std::string cons_arr_string(const Term & val, const Sort & sort) const;

  /** store a term in the internal maps and return the stored term
   * The returned term might be a different object than the input term.
   * For example, if a term with the same content has already been stored,
   * the old term is returned.
   */
  Term store_term(Term term) const;

  // parse result (sat, unsat, unknown) from solver's output
  Result str_to_result(std::string result) const;

  // parse actual value from a get-value response
  std::string strip_value_from_result(std::string result) const;

  /** helper function for bv constant
   * abs_decimal is the string represnentation of the absolute value of the
   * desired bv value. width is the bit-width returns a bv term of width `width`
   * whose value is (-1) * abs_decimal.
   * */
  Term make_non_negative_bv_const(std::string abs_decimal, uint width) const;

  /** helper function for bv constant
   * abs_decimal is the absolute value of the desired bit-vector.
   * width is the bit-width
   * returns a bv term of width `width` whose value is abs_value.
   * */
  Term make_non_negative_bv_const(int64_t abs_value, uint width) const;

  /** helper function for bv constant
   * abs_decimal is the string represnentation of the absolute value of the
   * desired bv value. width is the bit-width returns a bv term of width `width`
   * whose value is abs_decimal.
   * */
  Term make_negative_bv_const(std::string abs_decimal, uint width) const;

  /** helper function for bv constant
   * abs_decimal is the absolute value of the desired bit-vector.
   * width is the bit-width
   * returns a bv term of width `width` whose value is (-1) * abs_value.
   * */
  Term make_negative_bv_const(int64_t abs_value, uint width) const;

  // open a connection to the binary via a pipe
  void start_solver();
  // close the connection to the binary
  void close_solver();

  // internally defining and storing a function symbol
  void define_fun(std::string str,
                  smt::SortVec args_sorts,
                  smt::Sort res_sort,
                  smt::Term defining_term) const;

  // get the name of a term
  std::string get_name(Term t) const;

  // internal function to read solver's response
  std::string read_internal() const;

  // internal function to write to the solver's process
  void write_internal(std::string str) const;

  // run a command with the binary
  std::string run_command(std::string cmd,
                          bool verify_success_flag = true) const;

  // verify that we got `success`
  void verify_success(std::string result) const;

  // cmoputes  whether the current output from the solver
  // is done being read
  bool is_done(int just_read, std::string result) const;

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
};

}  // namespace smt
