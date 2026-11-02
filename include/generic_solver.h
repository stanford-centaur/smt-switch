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
** 2. The buffer size used to read the output of the solver binary
**    is limited to values between 2 and 256.
** 3. Generic solvers cannot be used in term transfer/translation.
** 4. Only on Linux is the solver process signalled when its parent dies.
** 5. All declarations made in the solver are global and permanent
**    (set-option :global-declarations true), meaning that popping
**    assertion levels does not remove them.
** 6. The solver follows the binary's SMT-LIB execution mode (start,
**    assert, sat, unsat) and refuses a command the mode does not permit,
**    such as get_value after anything but a sat or unknown check. A
**    command that needs a logic but arrives in start mode first sets the
**    logic ALL. A symbol, sort or term made after a check reaches the
**    binary only once the next command leaves the sat or unsat mode, so
**    the model can still be read; get_value refuses a term that uses a
**    symbol or sort declared since the check, which the model knows
**    nothing about.
**/

#pragma once

#include <sys/types.h>

#include <chrono>
#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "generic_datatype.h"
#include "result.h"
#include "smt_defs.h"
#include "solver.h"
#include "sort.h"
#include "term.h"

namespace smt {

/** The execution modes of SMT-LIB 2.6, Section 4.1.1. SAT and UNSAT are its
 * two query modes, entered by a check that answers sat or unknown, and
 * unsat, respectively.
 */
enum class SmtLibMode
{
  START,
  ASSERT,
  SAT,
  UNSAT
};

/** the name SMT-LIB gives a mode
 * @param mode the mode to name
 * @return "start", "assert", "sat" or "unsat"
 * @throws NotImplementedException for a value that is not an enumerator
 */
std::string to_string(SmtLibMode mode);

class GenericSolver : public AbsSmtSolver
{
 public:
  /** How long a solver is given, by default, to answer one command: a
   * backstop against a solver that has stopped talking to us rather than
   * a solving budget, so far longer than any command needs.
   */
  static const std::chrono::milliseconds default_response_timeout;

  /** Passed as `timeout` to wait indefinitely, giving up the
   * deadlock protection. Negative, because no real timeout can be.
   */
  static const std::chrono::milliseconds no_response_timeout;

  /** `timeout` bounds how long one command may go unanswered;
   * `no_response_timeout` waits forever.
   */
  GenericSolver(std::string solver_path,
                std::vector<std::string> args,
                std::chrono::milliseconds timeout = default_response_timeout,
                unsigned int buffer_size = 256);
  GenericSolver(const GenericSolver &) = delete;
  GenericSolver & operator=(const GenericSolver &) = delete;
  ~GenericSolver() override;

  /***************************************************************/
  /* methods from AbsSmtSolver that are currently not implemented*/
  /***************************************************************/
  // A datatype whose declarations refer to one another needs its sorts
  // before the constructors that use them, which this solver cannot
  // declare. One referring only to itself goes through add_selector_self.
  SortVec make_datatype_sorts(
      const std::vector<DatatypeDecl> & decls) const override;

  /***************************************************************/
  /* methods from AbsSmtSolver that are implemented              */
  /***************************************************************/
  // Declaring make_sort here at all would hide AbsSmtSolver's own overloads
  // from lookup on this type, so name them back in.
  using AbsSmtSolver::make_sort;
  Sort make_sort(const std::string name, std::uint64_t arity) const override;
  Sort make_sort(const SortKind sk) const override;
  Sort make_sort(const SortKind sk, std::uint64_t size) const override;
  Sort make_sort(const SortKind sk, const SortVec & sorts) const override;
  Sort make_sort(const Sort & sort_con, const SortVec & sorts) const override;
  Sort make_sort(const DatatypeDecl & d) const override;

  DatatypeDecl make_datatype_decl(const std::string & s) const override;
  DatatypeConstructorDecl make_datatype_constructor_decl(
      const std::string s) const override;
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

  // AbsSmtSolver's string-value overloads are not declared here, and a
  // declaration of the name would otherwise hide them from lookup on a
  // generic solver. Their default throws NotImplementedException.
  using AbsSmtSolver::make_term;

  Term make_term(bool b) const override;
  Term make_term(std::int64_t i, const Sort & sort) const override;
  Term make_term(const std::string val,
                 const Sort & sort,
                 std::uint64_t base = 10) const override;
  Term make_term(const Term & val, const Sort & sort) const override;
  Term make_symbol(const std::string name, const Sort & sort) override;
  Term get_symbol(const std::string & name) const override;
  Term make_param(const std::string name, const Sort & sort) const override;
  Term make_term(const Op op, const TermVec & terms) const override;
  Term get_value(const Term & t) const override;
  UnorderedTermMap get_array_values(const Term & arr,
                                    Term & out_const_base) const override;
  void get_unsat_assumptions(UnorderedTermSet & out) const override;

  void set_opt(const std::string option, const std::string value) override;
  void set_logic(const std::string logic) override;
  void assert_formula(const Term & t) override;
  Result check_sat() override;
  // Overriding check_sat_assuming hides the AbsSmtSolver template that
  // takes any range of Terms, so name it back in.
  using AbsSmtSolver::check_sat_assuming;
  Result check_sat_assuming(const TermVec & assumptions) override;

 protected:
  void do_push(std::uint64_t num) override;
  void do_pop(std::uint64_t num) override;
  void do_reset() override;
  void do_reset_assertions() override;

  /******************
   * helper methods *
   *******************/

  /** throw unless the solver is in `needed` mode
   * @param needed the mode the operation needs
   * @param operation the method being refused, for the message
   * @param reason what puts the solver in `needed` mode, for the message
   * @throws IncorrectUsageException if the solver is in another mode
   */
  void require_mode(SmtLibMode needed,
                    const std::string & operation,
                    const std::string & reason) const;

  /** send the declarations and definitions held back in the sat or unsat
   * mode, in the order they were made
   */
  void send_pending_commands() const;

  /** send a declaration or definition, or, in the sat or unsat mode, hold
   * it back until the next command that leaves the mode
   * @param cmd the declare-* or define-fun command
   * @return whether it was held back
   */
  bool send_or_hold(const std::string & cmd) const;

  /** send_or_hold for the command `(name args...)`
   * @param name the command's name
   * @param args its arguments, each written after a space
   * @return whether it was held back
   */
  template <class... Args>
  bool send_or_hold(std::string_view name, const Args &... args) const;

  /** whether a sort is, or is built from, one whose declaration is held
   * back
   * @param sort the sort to check
   * @return true if the sort mentions a held-back sort
   */
  bool uses_held_back_sort(const Sort & sort) const;

  /** the text standing for `term` in a get-value command: its name, or,
   * if it depends on definitions that are being held back, a let that
   * binds them first
   * @param term the term to be queried
   * @param operation the method asking, for the message
   * @return the term as it is to be written in the get-value
   * @throws IncorrectUsageException if the term uses a symbol or sort whose
   * declaration is held back, since the model has no value for one
   */
  std::string query_text(const Term & term,
                         const std::string & operation) const;

  /** Helper functions for the corresponding make_term
   * functions with the same arguments.
   * Also used to parse get_value responses.
   */
  Term make_value(bool b) const;
  Term make_value(std::int64_t i, const Sort & sort) const;
  Term make_value(const std::string val,
                  const Sort & sort,
                  std::uint64_t base = 10) const;

  // returns a string representation of a term in smtlib
  std::string to_smtlib_def(Term term) const;

  // parse solver's response from get-sat-assumptions
  UnorderedTermSet get_assumptions_from_string(std::string result) const;

  // the name to put in check-sat-assuming for an assumption: a literal's
  // own, or for any other formula a label asserted to imply it
  std::string assumption_name(const Term & assumption);

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

  /** translate one value from a get-value response into a term
   * @param value the value as the binary wrote it
   * @param sort the sort the value is read at
   * @return the term the string denotes
   */
  Term value_from_string(const std::string & value, const Sort & sort) const;

  /** helper function for bv constant
   * abs_decimal is the decimal string of the desired bv value.
   * returns the stored bv value of width `width` whose value is
   * abs_decimal, written as a binary literal of that width.
   * throws IncorrectUsageException if the value does not fit.
   * */
  Term make_non_negative_bv_const(std::string abs_decimal,
                                  unsigned int width) const;

  /** helper function for bv constant
   * abs_value is the desired bv value, which must not be negative.
   * returns the stored bv value of width `width` whose value is
   * abs_value, written as a binary literal of that width.
   * */
  Term make_non_negative_bv_const(std::int64_t abs_value,
                                  unsigned int width) const;

  /** helper function for bv constant
   * abs_decimal is the decimal string of the absolute value of the
   * desired bv value.
   * returns the stored bv value of width `width` whose value is
   * -abs_decimal, written in two's complement as a binary literal of that
   * width. throws IncorrectUsageException if the value does not fit.
   * */
  Term make_negative_bv_const(std::string abs_decimal,
                              unsigned int width) const;

  // start the binary and set the options every command relies on
  void start_solver();
  // start the binary and connect to it by pipes, setting nothing
  void launch_binary() const;
  // close the connection to the binary
  void close_solver() const;

  /** after the binary answered a command with an error, bring back its
   * state before it: a binary that died of the error is restarted.
   */
  void restore_binary() const;

  /** replace the binary with a new one given every command the old one
   * accepted. The model is lost, so sat or unsat mode becomes assert mode.
   * Throws InternalSolverException if the new binary does not accept them
   * all.
   */
  void restart_binary() const;

  // internally defining and storing a function symbol
  void define_fun(std::string str,
                  SortVec args_sorts,
                  Sort res_sort,
                  Term defining_term) const;

  // internal function to read solver's response; `cmd` names it in errors
  std::string read_internal(const std::string & cmd) const;

  // internal function to write to the solver's process
  void write_internal(std::string str) const;

  // take the first whole response out of `response_buffer`, if there is one
  bool take_response(std::string & response) const;

  // block until the solver has output, or throw when `deadline` passes;
  // `time_point::max()` never passes, so it waits forever
  void await_response(const std::chrono::steady_clock::time_point & deadline,
                      const std::string & cmd) const;

  // send a command and return the binary's trimmed response, as is
  std::string exchange(const std::string & cmd) const;

  // send a command and return the binary's reply unchecked, restoring the
  // binary after an error
  std::string send_command(const std::string & cmd) const;

  /** what a command does to the mode, after SMT-LIB 2.6, Section 4.1.1 */
  enum class CommandKind
  {
    // set-option, which leaves the mode as it is
    OPTION,
    // set-logic, which enters the assert mode
    LOGIC,
    // reset, which returns to the start mode
    RESET,
    // reset-assertions, which leaves the query modes for the assert mode
    RESET_ASSERTIONS,
    // a declaration, definition, assertion, push or pop, which enters the
    // assert mode
    ASSERTION,
    // check-sat or check-sat-assuming, which enters a query mode
    CHECK,
    // get-value or get-unsat-assumptions, which leaves the mode as it is
    GET
  };

  /** send a command and move to the mode it leads to
   * @param cmd the command
   * @param kind what the command does to the mode
   * @return the binary's reply, `success` for any kind but CHECK and GET
   * @throws IncorrectUsageException if the binary answers anything but
   * `success` to a kind other than CHECK and GET, SmtException if it
   * answers a GET with an error, and NotImplementedException if it answers
   * a CHECK with anything but sat, unsat or unknown
   *
   * The declarations and definitions held back since a check are sent
   * first, for any kind but OPTION, RESET and GET. An ASSERTION or CHECK
   * refused in the start mode is tried again after ALL, which some solvers
   * need. A command answered with `success` is recorded for a restore.
   */
  std::string run_command(const std::string & cmd, CommandKind kind) const;

  /** run_command for the command `(name args...)`
   * @param kind what the command does to the mode
   * @param name the command's name
   * @param args its arguments, each written after a space
   * @return the binary's reply, as for run_command
   */
  template <class... Args>
  std::string run_command(CommandKind kind,
                          std::string_view name,
                          const Args &... args) const;

  /***********
   * members *
   ***********/

  // path to the solver binary
  std::string path;

  // command line arguments for the binary
  std::vector<std::string> cmd_line_args;

  // variables used for running processes; the fds and pid are -1 when unset.
  // Restoring the binary in const methods starts a new process.
  mutable int inpipefd[2] = { -1, -1 };
  mutable int outpipefd[2] = { -1, -1 };
  mutable pid_t pid = -1;
  mutable int status = 0;
  // set once the binary has closed its output or its input
  mutable bool binary_exited_ = false;
  // every command the binary answered success to, in order, to bring a
  // new binary to the same state
  mutable std::vector<std::string> accepted_commands_;
  // filled by reads in const methods
  mutable std::vector<char> read_buf;

  // buffer size
  unsigned int read_buf_size;

  std::chrono::milliseconds response_timeout;

  // bytes read from the solver that no caller has taken yet: a read can
  // overshoot one response, and the rest belongs to the next command
  mutable std::string response_buffer;

  // maps between sort name and actual sort and vice versa
  mutable std::unordered_map<std::string, Sort> name_sort_map;
  mutable std::unordered_map<Sort, std::string> sort_name_map;

  // internal counter for naming terms
  mutable unsigned int term_counter = 0;

  // The terms the binary knows by a name it declared, under that name as
  // SMT-LIB writes it, so that a name the binary answers with finds its
  // term
  mutable std::unordered_map<std::string, Term> name_term_map;
  // How the binary is given each term made
  mutable std::unordered_map<Term, std::string> term_name_map;
  // The names users gave params, which the binary never sees
  mutable std::unordered_set<std::string> param_names_;

  // the binary's execution mode, as of the last command that succeeded
  mutable SmtLibMode mode_ = SmtLibMode::START;

  // declarations and definitions made in the sat or unsat mode, which
  // would leave it; in the order they were made, so each comes after
  // whatever it uses
  mutable std::vector<std::string> pending_commands_;
  // the terms and sorts those commands define or declare
  mutable UnorderedTermSet pending_definitions_;
  mutable UnorderedTermSet pending_symbols_;
  mutable std::unordered_set<std::string> pending_sort_names_;

  // labels standing in for assumptions that are not literals, and back
  UnorderedTermMap assumption_labels;
  UnorderedTermMap labelled_assumptions;

  // The datatype of each declaration, as two declarations can share a name
  mutable std::unordered_map<std::shared_ptr<GenericDatatypeDecl>,
                             std::shared_ptr<GenericDatatype>>
      decl_datatype_map;
  // The name of each datatype
  mutable std::unordered_map<std::shared_ptr<GenericDatatype>, std::string>
      datatype_name_map;
};

}  // namespace smt
