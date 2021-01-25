/*********************                                                        */
/*! \file generic_solver.cpp
** \verbatim
** Top contributors (to current version):
**   Yoni Zohar
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
** 
**
** \brief A class that represents a generic solver
**
**/

/* Uses code to interact with a process from:
** https://stackoverflow.com/a/6172578/1364765
*/

// generic solvers are not supported on macos
#ifndef __APPLE__

#include "generic_solver.h"

#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/wait.h>
#include <unistd.h>

#include <algorithm>

#include "assert.h"
#include "smtlib_utils.h"
#include "sort.h"
#include "sort_inference.h"
#include "utils.h"

using namespace std;

namespace smt {

// helper functions
bool is_new_line(char c) { return (c == '\n' || c == '\r' || c == 0); }

// from: https://stackoverflow.com/a/36000453/1364765
std::string & trim(std::string & str)
{
  // right trim
  while (str.length() > 0
         && (str[str.length() - 1] == ' ' || str[str.length() - 1] == '\t'
             || str[str.length() - 1] == '\n'))
    str.erase(str.length() - 1, 1);

  // left trim
  while (str.length() > 0
         && (str[0] == ' ' || str[0] == '\t' || str[0] == '\n'))
    str.erase(0, 1);
  return str;
}

// class methods implementation
GenericSolver::GenericSolver(string path,
                             vector<string> cmd_line_args,
                             uint write_buf_size,
                             uint read_buf_size)
    : AbsSmtSolver(SolverEnum::GENERIC_SOLVER),
      path(path),
      cmd_line_args(cmd_line_args),
      write_buf_size(write_buf_size),
      read_buf_size(read_buf_size),
      name_sort_map(new unordered_map<string, Sort>()),
      sort_name_map(new unordered_map<Sort, string>()),
      name_term_map(new unordered_map<string, Term>()),
      term_name_map(new unordered_map<Term, string>())
{
  term_counter = new uint;
  //allocate memory for the buffers
  write_buf = new char[write_buf_size];
  read_buf = new char[read_buf_size];

  //make sure allocation was successful
  assert(write_buf != NULL);
  assert(read_buf != NULL);
  //initialize write_buf
  for (int i=0; i < write_buf_size; i++) {
    write_buf[i]=0;
  }
  //initialize read_buf
  for (int i=0; i < read_buf_size; i++) {
    read_buf[i]=0;
  }

  // start the process with the solver binary
  start_solver();
}

GenericSolver::~GenericSolver() {
  //deallocate the buffers memory
  delete write_buf;
  delete read_buf;
  delete term_counter;
  // close the solver process
  close_solver();
}

void GenericSolver::start_solver() {
  pid = 0;

  pipe(inpipefd);
  pipe(outpipefd);
  pid = fork();
  if (pid == 0)
  {
    // Child
    dup2(outpipefd[0], STDIN_FILENO);
    dup2(inpipefd[1], STDOUT_FILENO);
    dup2(inpipefd[1], STDERR_FILENO);

    // ask kernel to deliver SIGTERM in case the parent dies
    prctl(PR_SET_PDEATHSIG, SIGTERM);
    //    fcntl(inpipefd[1], F_SETFL, O_NONBLOCK);
    // The following part is based on:
    // https://stackoverflow.com/a/5797901/1364765 The execv command expects an
    // array, and so we create one. First element is the program name, last
    // element is NULL, and in between are the elements of cmd_line_args, casted
    // to (char*) from std::string. Here we identify the program name with its
    // path.
    const char ** argv = new const char *[cmd_line_args.size() + 2];
    argv[0] = path.c_str();
    for (int i = 1; i <= cmd_line_args.size(); i++)
    {
      argv[i] = cmd_line_args[i - 1].c_str();
    }
    argv[cmd_line_args.size() + 1] = NULL;
    execv(path.c_str(), (char **)argv);
    // Nothing below this line should be executed by child process. If so,
    // it means that the execl function wasn't successfull, so lets exit:
    string msg("failure to run binary: ");
    msg += path;
    throw IncorrectUsageException(msg);
    exit(1);
  }
  // close unused pipe ends
  close(outpipefd[0]);
  close(inpipefd[1]);
  set_opt("print-success", "true");
}

void GenericSolver::write_internal(string str) const
{
  // track how many charas were written so far
  uint written_chars = 0;
  // continue writing  until entire str was written
  while (written_chars < str.size())
  {
    // how many characters are there left to write
    uint remaining = str.size() - written_chars;
    // how many characters are we writing in this iteration
    uint substr_size;
    if (remaining < write_buf_size)
    {
      substr_size = remaining;
    }
    else
    {
      substr_size = write_buf_size;
    }
    // write
    strcpy(write_buf, str.substr(written_chars, substr_size).c_str());
    write(outpipefd[1], write_buf, substr_size);
    written_chars += substr_size;
  }
}

bool GenericSolver::is_done(int just_read, std::string result) const
{
  bool done = false;
  int count = 0;
  // if we didn't read anything now, the command is done executing
  if (just_read == 0)
  {
    done = true;
  }
  else if (result[0] == '(')
  {
    // if the output of the solver starts with '('
    // we will be done only when we see the matching ')'
    for (int i = 0; i < result.size(); i++)
    {
      if (result[i] == '(')
      {
        count++;
      }
      else if (result[i] == ')')
      {
        count--;
      }
    }
    done = (count == 0) && is_new_line(result[result.size() - 1]);
  }
  else
  {
    // if the output of the solver does not start with '('
    // we will be done when we reach a newline character
    assert(just_read <= read_buf_size);
    for (int i = 0; i < just_read; i++)
    {
      if (is_new_line(read_buf[i]))
      {
        done = true;
      }
    }
  }
  return done;
}

string GenericSolver::read_internal() const
{
  string result = "";
  bool done = false;
  // read to the buffer until no more output to read
  while (!done)
  {
    // read command, and how many chars were read.
    int just_read = read(inpipefd[0], read_buf, read_buf_size);
    // store the content and trim it
    string read_buf_str(read_buf);
    read_buf_str = read_buf_str.substr(0, read_buf_size);
    result = result.append(read_buf_str);
    done = is_done(just_read, result);
    // clear buffer
    for (int i = 0; i < read_buf_size; i++)
    {
      read_buf[i] = 0;
    }
  }
  // normalize outout of solver:
  // - no newlines in the middle of the content
  // - no double spaces
  while (result.find("\n") != string::npos)
  {
    result.replace(result.find("\n"), 1, " ");
  }
  while (result.find("  ") != string::npos)
  {
    result.replace(result.find("  "), 2, " ");
  }
  return result;
}

string GenericSolver::run_command(string cmd, bool verify_success_flag) const
{
  // adding a newline to simulate an "enter" hit.
  cmd = cmd + "\n";
  // writing the cmd string to the process
  write_internal(cmd);
  // reading the result
  string result = read_internal();
  result = trim(result);
  // verify success if needed
  if (verify_success_flag)
  {
    verify_success(result);
  }
  return result;
}

void GenericSolver::verify_success(string result) const
{
  if (result == "success")
  {
    return;
  }
  else
  {
    throw IncorrectUsageException(
        "The command did not end with a success message from the solver. The "
        "result was: "
        + result);
  }
}

void GenericSolver::close_solver() {
  kill(pid, SIGKILL);
  waitpid(pid, &status, 0);
}

void GenericSolver::define_fun(std::string name,
                               SortVec args_sorts,
                               Sort res_sort,
                               Term defining_term) const
{
  // we only use functions without parameters
  // (like define-const)
  assert(args_sorts.size() == 0);
  assert(sort_name_map->find(res_sort) != sort_name_map->end());
  // send a define-fun to the binary
  run_command("(" + DEFINE_FUN_STR + " " + name + " () "
              + (*sort_name_map)[res_sort] + " " + to_smtlib_def(defining_term)
              + ")");
}

std::string GenericSolver::to_smtlib_def(Term term) const
{
  // cast to generic term
  shared_ptr<GenericTerm> gt = static_pointer_cast<GenericTerm>(term);
  // generic terms with no operators are represented by their
  // name.
  if (gt->get_op().is_null())
  {
    return gt->to_string();
  }
  else
  {
    // generic terms with operators are written as s-expressions.
    string result = "(";
    // The Apply operator is ignored and the
    // function being applied is used instead.
    result +=
        ((term->get_op().prim_op == Apply) ? "" : term->get_op().to_string());
    // For quantifiers we separate the bound variables list
    // and the formula body.
    if (term->get_op().prim_op == Forall || term->get_op().prim_op == Exists)
    {
      result += " ((" + (*term_name_map)[gt->get_children()[0]] + " "
                + (*sort_name_map)[gt->get_children()[0]->get_sort()] + ")) "
                + (*term_name_map)[gt->get_children()[1]];
    }
    else
    {
      // in the general case (other than quantifiers
      // and Apply), we use ordinary
      // s-expressions notation and write a
      // space-separated list of arguments.
      for (auto c : gt->get_children())
      {
        result += " " + (*term_name_map)[c];
      }
    }
    result += ")";
    return result;
  }
}

Sort GenericSolver::make_sort(const Sort & sort_con, const SortVec & sorts) const {
  // When constructing a sort, the sort constructor
  // must have been already processed
  assert(sort_name_map->find(sort_con) != sort_name_map->end());
  // The arity of the sort constructor must match
  // the number of arguments
  assert(sort_con->get_arity() == sorts.size());

  // All the input sorts must have been processed
  for (Sort sort : sorts)
  {
    assert(sort_name_map->find(sort) != sort_name_map->end());
  }

  // creating the new sort
  Sort sort = make_uninterpreted_generic_sort(sort_con, sorts);

  // note that there is no need to communicate anything
  // to the solver yet. When the sort will be used,
  // we will print the right name to the solver.

  // assigning a name to the new sort
  string name = sort->get_uninterpreted_name();

  // store in the map if missing, and return the new sort
  if (name_sort_map->find(name) != name_sort_map->end())
  {
    return (*name_sort_map)[name];
  }
  else
  {
    (*name_sort_map)[name] = sort;
    (*sort_name_map)[sort] = name;
    return sort;
  }
}

Sort GenericSolver::make_sort(const std::string name, uint64_t arity) const {
  // when creating a new uninterpreted sort, the name
  // must be new.
  if (name_sort_map->find(name) == name_sort_map->end())
  {
    // create the sort
    Sort sort = make_uninterpreted_generic_sort(name, arity);
    // store the sort and the name in the maps
    (*name_sort_map)[name] = sort;
    (*sort_name_map)[sort] = name;
    // declare the sort to the binary of the solver
    run_command("(" + DECLARE_SORT_STR + " " + name + " "
                + std::to_string(arity) + ")");
    return sort;
  }
  else
  {
    throw IncorrectUsageException(string("sort name: ") + name
                                  + string(" already taken"));
  }
}

Sort GenericSolver::make_sort(const SortKind sk) const
{
  // create the sort
  Sort sort = make_generic_sort(sk);
  // compute the name of the sort
  string name = sort->to_string();

  // note that nothing needs to be communicated to the solver,
  // as in this case the sort is built in.

  // store in local maps if needed, and return the sort
  if (name_sort_map->find(name) == name_sort_map->end())
  {
    (*name_sort_map)[name] = sort;
    (*sort_name_map)[sort] = name;
    return sort;
  }
  else
  {
    return name_sort_map->at(name);
  }
}

Sort GenericSolver::make_sort(const SortKind sk, uint64_t size) const
{
  // create the sort
  Sort sort = make_generic_sort(sk, size);
  // compute the name
  string name = sort->to_string();

  // note that nothing needs to be communicated to the solver,
  // as in this case the sort is built in.

  // store in maps if needed and return the sort
  if (name_sort_map->find(name) == name_sort_map->end())
  {
    (*name_sort_map)[name] = sort;
    (*sort_name_map)[sort] = name;
    return sort;
  }
  else
  {
    return name_sort_map->at(name);
  }
}

Sort GenericSolver::make_sort(const SortKind sk, const Sort & sort1) const
{
  return make_sort(sk, SortVec({ sort1 }));
}

Sort GenericSolver::make_sort(const SortKind sk,
                              const Sort & sort1,
                              const Sort & sort2) const
{
  return make_sort(sk, SortVec({ sort1, sort2 }));
}

Sort GenericSolver::make_sort(const SortKind sk,
                              const Sort & sort1,
                              const Sort & sort2,
                              const Sort & sort3) const
{
  return make_sort(sk, SortVec({ sort1, sort2, sort3 }));
}

Sort GenericSolver::make_sort(SortKind sk, const SortVec & sorts) const
{
  // create the sort
  Sort sort = make_generic_sort(sk, sorts);
  // compute the name
  string name = sort->to_string();

  // note that nothing needs to be communicated to the solver,
  // as in this case the sort is built in, or can used
  // by combining sorts that were already defined.

  // store in maps if needed and return the sort
  if (name_sort_map->find(name) == name_sort_map->end())
  {
    (*name_sort_map)[name] = sort;
    (*sort_name_map)[sort] = name;
    return sort;
  }
  else
  {
    return name_sort_map->at(name);
  }
}

Sort GenericSolver::make_sort(const DatatypeDecl & d) const
{
  assert(false);  
}
  
DatatypeDecl GenericSolver::make_datatype_decl(const std::string & s)
  {
  assert(false);  
  }
DatatypeConstructorDecl GenericSolver::make_datatype_constructor_decl(
    const std::string s)
{
  assert(false);  
}
  
void GenericSolver::add_constructor(DatatypeDecl & dt, const DatatypeConstructorDecl & con) const
  {
  assert(false);  
}
void GenericSolver::add_selector(DatatypeConstructorDecl & dt, const std::string & name, const Sort & s) const
{
  assert(false);  
}
  
void GenericSolver::add_selector_self(DatatypeConstructorDecl & dt, const std::string & name) const
  {
  assert(false);  
}

Term GenericSolver::get_constructor(const Sort & s, std::string name) const
{
  assert(false);  
}

  
Term GenericSolver::get_tester(const Sort & s, std::string name) const
{
  assert(false);  
}

Term GenericSolver::get_selector(const Sort & s, std::string con, std::string name) const
{
  assert(false);  
}

std::string GenericSolver::get_name(Term term) const
{
  // the names of the terms are `t_i` with a running `i`.
  // These names are used for `define-fun` commands.
  *term_counter = (*term_counter) + 1;
  return "t_" + std::to_string((*term_counter));
}

Term GenericSolver::store_term(Term term) const
{
  // cast the term to a GenericTerm
  shared_ptr<GenericTerm> gterm = static_pointer_cast<GenericTerm>(term);
  // store the term in the maps in case it is not there already
  if (term_name_map->find(gterm) == term_name_map->end())
  {
    string name;
    // ground terms are communicated to the binary
    // using a define-fun command.
    // In future instances of this term, we will use the name
    // of the defined function.
    // For example: if `term` is `0`, and `name` is `t1`,
    // we send a command:
    // `(define-fun t1 () Int 0)`
    // If in the future we see a term `0+0`, it will
    // be sent to the solver as `(+ t1 t1)`.
    //
    // However, terms with bound variables cannot be given to
    // a define-fun command. For them, we store
    // their actual definition.
    // In future instances, the entire definition will be used.
    if (gterm->is_ground())
    {
      name = get_name(gterm);
      define_fun(name, SortVec{}, gterm->get_sort(), gterm);
    }
    else
    {
      name = to_smtlib_def(gterm);
    }
    (*name_term_map)[name] = gterm;
    (*term_name_map)[gterm] = name;
  }
  // return the term from the internal map
  string name = (*term_name_map)[gterm];
  return (*name_term_map)[name];
}

Term GenericSolver::make_non_negative_bv_const(string abs_decimal,
                                               uint width) const
{
  Sort bvsort = make_sort(BV, width);
  string repr = "(_ bv" + abs_decimal + " " + std::to_string(width) + ")";
  Term term = std::make_shared<GenericTerm>(bvsort, Op(), TermVec{}, repr);
  return store_term(term);
}

Term GenericSolver::make_non_negative_bv_const(int64_t i, uint width) const
{
  assert(i >= 0);
  return make_non_negative_bv_const(std::to_string(i), width);
}

Term GenericSolver::make_negative_bv_const(string abs_decimal, uint width) const
{
  Term zero = make_non_negative_bv_const("0", width);
  Term abs = make_non_negative_bv_const(abs_decimal, width);
  Term result = make_term(BVSub, zero, abs);
  return store_term(result);
}

Term GenericSolver::make_negative_bv_const(int64_t abs_value, uint width) const
{
  assert(abs_value >= 0);
  return make_negative_bv_const(std::to_string(abs_value), width);
}

Term GenericSolver::make_term(bool b) const
{
  // create a generic term that represents `b`.
  Sort boolsort = make_sort(BOOL);
  Term term = std::make_shared<GenericTerm>(
      boolsort, Op(), TermVec{}, b ? "true" : "false");
  return store_term(term);
}

Term GenericSolver::make_term(int64_t i, const Sort & sort) const
{
  SortKind sk = sort->get_sort_kind();
  assert(sk == BV || sk == INT || sk == REAL);
  if (sk == INT || sk == REAL)
  {
    string repr = std::to_string(i);
    Term term = std::make_shared<GenericTerm>(sort, Op(), TermVec{}, repr);
    return store_term(term);
  }
  else
  {
    // sk == BV
    if (i < 0)
    {
      int64_t abs_value = i * (-1);
      Term term = make_negative_bv_const(abs_value, sort->get_width());
      return store_term(term);
    }
    else
    {
      Term term = make_non_negative_bv_const(i, sort->get_width());
      return store_term(term);
    }
  }
}

Term GenericSolver::make_term(const string name,
                              const Sort & sort,
                              uint64_t base) const
{
  SortKind sk = sort->get_sort_kind();
  assert(sk == BV || sk == INT || sk == REAL);
  assert(base == 2 || base == 10 | base == 16);
  string repr;
  if (sk == INT || sk == REAL)
  {
    assert(base == 10);
    repr = name;
    Term term = std::make_shared<GenericTerm>(sort, Op(), TermVec{}, repr);
    return store_term(term);
  }
  else
  {
    // sk == BV
    if (base == 10)
    {
      if (name.find("-") == 0)
      {
        string abs_decimal = name.substr(1);
        return make_negative_bv_const(abs_decimal, sort->get_width());
      }
      else
      {
        return make_non_negative_bv_const(name, sort->get_width());
      }
    }
    else
    {
      // base = 2 or 16
      if (base == 2)
      {
        repr = "#b" + name;
      }
      else if (base == 16)
      {
        repr = "#x" + name;
      }
      Term term = std::make_shared<GenericTerm>(sort, Op(), TermVec{}, repr);
      return store_term(term);
    }
  }
}

string GenericSolver::cons_arr_string(const Term & val, const Sort & sort) const
{
  assert(term_name_map->find(val) != term_name_map->end());
  assert(sort_name_map->find(sort) != sort_name_map->end());
  return "((as const " + (*sort_name_map)[sort] + ") " + val->to_string()
         + ") ";
}

Term GenericSolver::make_term(const Term & val, const Sort & sort) const
{
  assert(sort->get_sort_kind() == ARRAY);
  assert(sort->get_elemsort() == val->get_sort());
  Term term = std::make_shared<GenericTerm>(
      sort, Op(), TermVec{ val }, cons_arr_string(val, sort));
  return store_term(term);
}

Term GenericSolver::make_symbol(const string name, const Sort & sort)
{
  // make sure that the symbol name is not aready taken.
  if (name_term_map->find(name) != name_term_map->end())
  {
    throw IncorrectUsageException(
        string("symbol name: ") + name
        + string(" already taken, either by another symbol or by a param"));
  }

  // create the sumbol and store it in the maps
  Term term = std::make_shared<GenericTerm>(sort, Op(), TermVec{}, name, true);
  (*name_term_map)[name] = term;
  (*term_name_map)[term] = name;

  // communicate the creation of the symbol to the binary of the solver.
  // When the sort is not a fucntion, we specify an empty domain.
  // Otherwise, the name of the sort includes the domain.
  run_command("(" + DECLARE_FUN_STR + " " + name
              + (sort->get_sort_kind() == FUNCTION ? " " : " () ")
              + (*sort_name_map)[sort] + ")");

  // return the created symbol as a term
  return (*name_term_map)[name];
}

Term GenericSolver::make_param(const string name, const Sort & sort)
{
  if (name_term_map->find(name) != name_term_map->end())
  {
    throw IncorrectUsageException(
        string("param name: ") + name
        + string(" already taken, either by another param or by a symbol"));
  }
  Term term = std::make_shared<GenericTerm>(sort, Op(), TermVec{}, name, false);
  (*name_term_map)[name] = term;
  (*term_name_map)[term] = name;
  return (*name_term_map)[name];
}

Term GenericSolver::make_term(const Op op, const Term & t) const
{
  return make_term(op, TermVec({ t }));
}

Term GenericSolver::make_term(const Op op,
                              const Term & t1,
                              const Term & t2) const
{
  return make_term(op, TermVec({ t1, t2 }));
}

Term GenericSolver::make_term(const Op op,
                              const Term & t1,
                              const Term & t2,
                              const Term & t3) const
{
  return make_term(op, TermVec({ t1, t2, t3 }));
}

Term GenericSolver::make_term(const Op op, const TermVec & terms) const
{
  Sort sort = compute_sort(op, this, terms);
  string repr = "(" + op.to_string();
  for (int i = 0; i < terms.size(); i++)
  {
    assert((*term_name_map).find(terms[i]) != (*term_name_map).end());
    repr += " " + (*term_name_map)[terms[i]];
  }
  repr += ")";
  Term term = std::make_shared<GenericTerm>(sort, op, terms, repr);
  Term stored_term = store_term(term);
  return stored_term;
}

Term GenericSolver::get_value(const Term & t) const
{
  assert(false);
}

void GenericSolver::get_unsat_core(UnorderedTermSet & out)
{
  assert(false);
}

UnorderedTermMap GenericSolver::get_array_values(const Term & arr,
                                                 Term & out_const_base) const
{
  assert(false);  
}

void GenericSolver::reset()
{
  string result = run_command("(" + RESET_STR + ")");
}

void GenericSolver::set_opt(const std::string option, const std::string value)
{
  run_command("(" + SET_OPTION_STR + " :" + option + " " + value + ")");
}

void GenericSolver::set_logic(const std::string logic)
{
  run_command("(" + SET_LOGIC_STR + " " + logic + ")");
}

void GenericSolver::assert_formula(const Term & t)
{
  // cast to generic term, as we need to print it to the solver
  shared_ptr<GenericTerm> lt = static_pointer_cast<GenericTerm>(t);

  // obtain the name of the term from the internal map
  assert(term_name_map->find(lt) != term_name_map->end());
  string name = (*term_name_map)[lt];

  // communicate the assertion to the binary of the solver
  run_command("(" + ASSERT_STR + " " + name + ")");
}

Result GenericSolver::str_to_result(string result) const
{
  if (result == "unsat")
  {
    return Result(UNSAT);
  }
  else if (result == "sat")
  {
    return Result(SAT);
  }
  else if (result == "unknown")
  {
    return Result(UNKNOWN);
  }
  else
  {
    throw NotImplementedException(
        "Unimplemented result type from the generic solver. The result was: "
        + result);
  }
}

Result GenericSolver::check_sat()
{
  string result = run_command("(" + CHECK_SAT_STR + ")", false);
  Result r = str_to_result(result);
  return r;
}

Result GenericSolver::check_sat_assuming(const TermVec & assumptions)
{
  assert(false);
}

void GenericSolver::push(uint64_t num)
  {
    string result =
        run_command("(" + PUSH_STR + " " + std::to_string(num) + ")");
  }

void GenericSolver::pop(uint64_t num)
{
  string result = run_command("(" + POP_STR + " " + std::to_string(num) + ")");
}

void GenericSolver::reset_assertions()
  {
    string result = run_command("(" + RESET_ASSERTIONS_STR + ")");
  }

}  // namespace smt

#endif  // __APPLE__
