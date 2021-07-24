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
      term_name_map(new unordered_map<Term, string>()),
      name_datatype_map(
          new unordered_map<string, std::shared_ptr<GenericDatatype>>()),
      datatype_name_map(
          new unordered_map<std::shared_ptr<GenericDatatype>, string>())
{
  // Buffer sizes over 256 caused issues in tests.
  // Until this is investigated, we support a conservative
  // limit of 256.
  // Similarly for buffers of size 1.
  if (write_buf_size < 2 || write_buf_size > 256 || read_buf_size < 2
      || read_buf_size > 256)
  {
    string msg(
        "Generic Solvers require a buffer size of at least 2 and at most 256.");
    throw IncorrectUsageException(msg);
  }
  term_counter = new uint;
  //allocate memory for the buffers
  write_buf = new char[write_buf_size];
  read_buf = new char[read_buf_size];

  // sure allocation was successful
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
  cout << "command sent:" << endl;
  cout << "(" + DEFINE_FUN_STR + " " + name + " () "
    + (*sort_name_map)[res_sort] + " " + to_smtlib_def(defining_term)
    + ")" << endl;
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
  throw NotImplementedException(
      "Sort constructor are not supported by generic solvers");
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
  shared_ptr<GenericDatatypeDecl> gdt_decl =
      static_pointer_cast<GenericDatatypeDecl>(d);
  string dt_decl_name = gdt_decl->get_name();
  assert(name_datatype_map->find(dt_decl_name) != name_datatype_map->end());
  shared_ptr<GenericDatatype> curr_dt = (*name_datatype_map)[dt_decl_name];
  if (name_sort_map->find(dt_decl_name) == name_sort_map->end())
  {
    // Exact functionality of make_genericsort, without the linking
    // errors (undefined reference when I call a new
    // make_generic_sort).
    //Sort dt_sort = make_generic_sort(curr_dt);
    Sort dt_sort = make_shared<GenericDatatypeSort>(curr_dt);
    // Replaces the sort of any selectors with a false finalized field
    // with dt_sort and sets finalized to true.
    curr_dt->change_sort_of_selector(dt_sort);

    std::string to_solver = "(" + DECLARE_DATATYPE_STR + " ((";
    to_solver += dt_decl_name;
    to_solver += " 0)) (\n";
    to_solver += "(";
    // build string for each constructor
    for (unsigned long i = 0; i < curr_dt->get_cons_vector().size(); ++i)
    {
      DatatypeConstructorDecl curr_dt_cons_decl = curr_dt->get_cons_vector()[i];
      to_solver += " ("
                   + static_pointer_cast<GenericDatatypeConstructorDecl>(
                         curr_dt_cons_decl)
                         ->get_name();
      // adjust string for each selector
      for (unsigned long f = 0;
           f < static_pointer_cast<GenericDatatypeConstructorDecl>(
                   curr_dt_cons_decl)
                   ->get_selector_vector()
                   .size();
           ++f)
      {
        to_solver += " ( "
                     + static_pointer_cast<GenericDatatypeConstructorDecl>(
                           curr_dt_cons_decl)
                           ->get_selector_vector()[f]
                           .name;
        to_solver += " "
                     + (static_pointer_cast<GenericDatatypeConstructorDecl>(
                            curr_dt_cons_decl)
                            ->get_selector_vector()[f]
                            .sort)
                           ->to_string()
                     + " )";
      }

      to_solver += ")";
    }
    to_solver += ")\n))";
    assert(name_sort_map->find(dt_decl_name) == name_sort_map->end());
    (*name_sort_map)[dt_decl_name] = dt_sort;
    (*sort_name_map)[dt_sort] = dt_decl_name;
    run_command(to_solver);

    return dt_sort;
  }
  else
  {
    throw IncorrectUsageException(string("sort name: ") + dt_decl_name
                                  + string(" already taken"));
  }
}

DatatypeDecl GenericSolver::make_datatype_decl(const std::string & s)
{
  DatatypeDecl new_dt_decl = make_shared<GenericDatatypeDecl>(s);
  shared_ptr<GenericDatatype> new_dt =
      shared_ptr<GenericDatatype>(new GenericDatatype(new_dt_decl));
  (*name_datatype_map)[s] = new_dt;
  (*datatype_name_map)[new_dt] = s;
  return new_dt_decl;
}
DatatypeConstructorDecl GenericSolver::make_datatype_constructor_decl(
    const std::string s)
{
  shared_ptr<GenericDatatypeConstructorDecl> new_dt_cons_decl =
      shared_ptr<GenericDatatypeConstructorDecl>(
          new GenericDatatypeConstructorDecl(s));
  return new_dt_cons_decl;
}

void GenericSolver::add_constructor(DatatypeDecl & dt, const DatatypeConstructorDecl & con) const
  {
    shared_ptr<GenericDatatypeDecl> gdt_decl =
        static_pointer_cast<GenericDatatypeDecl>(dt);
    string name = gdt_decl->get_name();
    auto gdt = (*name_datatype_map)[name];
    gdt->add_constructor(con);
}

void GenericSolver::add_selector(DatatypeConstructorDecl & dt, const std::string & name, const Sort & s) const
{
  shared_ptr<SelectorComponents> newSelector =
      make_shared<SelectorComponents>();
  newSelector->name = name;
  newSelector->sort = s;
  newSelector->finalized = true;
  shared_ptr<GenericDatatypeConstructorDecl> gdtc =
      static_pointer_cast<GenericDatatypeConstructorDecl>(dt);
  gdtc->add_new_selector(*newSelector);
}
  
void GenericSolver::add_selector_self(DatatypeConstructorDecl & dt, const std::string & name) const
  {
    shared_ptr<SelectorComponents> newSelector =
        make_shared<SelectorComponents>();
    shared_ptr<GenericDatatypeConstructorDecl> gdt_cons =
        static_pointer_cast<GenericDatatypeConstructorDecl>(dt);
    string dt_decl_name = gdt_cons->get_dt_name();

    newSelector->name = name;
    // Sets the sort to be a placeholder value until the self sort is
    // constructed.
    newSelector->sort = make_shared<GenericSort>(name);
    // This indicates that the sort in this selector will eventually
    // be replaced
    newSelector->finalized = false;
    assert(name_datatype_map->find(dt_decl_name) != name_datatype_map->end());
    shared_ptr<GenericDatatype> curr_dt = (*name_datatype_map)[dt_decl_name];
    gdt_cons->add_new_selector(*newSelector);
}

Term GenericSolver::get_constructor(const Sort & s, std::string name) const
{
  shared_ptr<GenericDatatype> dt = static_pointer_cast<GenericDatatype>(s->get_datatype());
  bool found = false;
  for (int i = 0; i < dt->get_num_constructors(); ++i) {
    if (static_pointer_cast<GenericDatatypeConstructorDecl>(dt->get_cons_vector()[i])->get_name() == name) {
      found = true;
    }
  }
  if (!found) {
    throw "Constructor not in datatype";
  }
  Sort cons_sort = make_generic_sort(CONSTRUCTOR, name);
  Term new_term = std::make_shared<GenericTerm>(cons_sort, Op(), TermVec{}, name, true);
  (*name_term_map)[name] = new_term;
  (*term_name_map)[new_term] = name;
  return (*name_term_map)[name];
  
}

  
Term GenericSolver::get_tester(const Sort & s, std::string name) const
{
  Sort cons_sort = make_generic_sort(SELECTOR, name);
  Term new_term = std::make_shared<GenericTerm>(cons_sort, Op(), TermVec{}, name, true);
  (*name_term_map)[name] = new_term;
  (*term_name_map)[new_term] = name;
  return (*name_term_map)[name];
  
  
}

Term GenericSolver::get_selector(const Sort & s, std::string con, std::string name) const
{
  throw NotImplementedException("Generic Solvers do not support datatypes");
  
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
      cout << "print ground name" << endl;
      cout << name << endl;
      cout << gterm->get_sort()->to_string() << endl;
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
  return term;
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
  return result;
}

Term GenericSolver::make_negative_bv_const(int64_t abs_value, uint width) const
{
  assert(abs_value >= 0);
  return make_negative_bv_const(std::to_string(abs_value), width);
}

Term GenericSolver::make_term(bool b) const
{
  Term value_term = make_value(b);
  return store_term(value_term);
}

Term GenericSolver::make_value(bool b) const
{
  // create a generic term that represents `b`.
  Sort boolsort = make_sort(BOOL);
  Term term = std::make_shared<GenericTerm>(
      boolsort, Op(), TermVec{}, b ? "true" : "false");
  return term;
}

Term GenericSolver::make_term(int64_t i, const Sort & sort) const
{
  Term value_term = make_value(i, sort);
  return store_term(value_term);
}

Term GenericSolver::make_value(int64_t i, const Sort & sort) const
{
  SortKind sk = sort->get_sort_kind();
  assert(sk == BV || sk == INT || sk == REAL);
  if (sk == INT || sk == REAL)
  {
    string repr = std::to_string(i);
    Term term = std::make_shared<GenericTerm>(sort, Op(), TermVec{}, repr);
    return term;
  }
  else
  {
    // sk == BV
    if (i < 0)
    {
      int64_t abs_value = i * (-1);
      Term term = make_negative_bv_const(abs_value, sort->get_width());
      return term;
    }
    else
    {
      Term term = make_non_negative_bv_const(i, sort->get_width());
      return term;
    }
  }
}

Term GenericSolver::make_term(const string val,
                              const Sort & sort,
                              uint64_t base) const
{
  Term value_term = make_value(val, sort, base);
  return store_term(value_term);
}

Term GenericSolver::make_value(const string val,
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
    repr = val;
    Term term = std::make_shared<GenericTerm>(sort, Op(), TermVec{}, repr);
    return term;
  }
  else
  {
    // sk == BV
    if (base == 10)
    {
      if (val.find("-") == 0)
      {
        string abs_decimal = val.substr(1);
        return make_negative_bv_const(abs_decimal, sort->get_width());
      }
      else
      {
        return make_non_negative_bv_const(val, sort->get_width());
      }
    }
    else
    {
      // base = 2 or 16
      if (base == 2)
      {
        repr = "#b" + val;
      }
      else if (base == 16)
      {
        repr = "#x" + val;
      }
      Term term = std::make_shared<GenericTerm>(sort, Op(), TermVec{}, repr);
      return term;
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
  cout << "pre compute sort" << endl;
  Sort sort = compute_sort(op, this, terms);
  cout << "post compute sort" << endl;
  string repr = "(" + op.to_string();
  for (int i = 0; i < terms.size(); i++)
  {
    assert((*term_name_map).find(terms[i]) != (*term_name_map).end());
    repr += " " + (*term_name_map)[terms[i]];
  }
  repr += ")";
  cout << "repr" << endl;
  cout << repr << endl;
  Term term = std::make_shared<GenericTerm>(sort, op, terms, repr);
  Term stored_term = store_term(term);
  return stored_term;
}

Term GenericSolver::get_value(const Term & t) const
{
  // we do not support getting array values, function values, and uninterpreted
  // values.
  Sort sort = t->get_sort();
  assert(sort->get_sort_kind() != ARRAY && sort->get_sort_kind() != FUNCTION
         && sort->get_sort_kind() != UNINTERPRETED);

  // get the name of the term (the way the term is defined in the solver)
  assert(term_name_map->find(t) != term_name_map->end());
  string name = (*term_name_map)[t];

  // ask the binary for the value and parse it
  string result = run_command("(" + GET_VALUE_STR + " (" + name + "))", false);

  // check that there was no error
  check_no_error(result);

  string value = strip_value_from_result(result);

  // translate the string representation of the result into a term
  Term resulting_term;
  // for bit-vectors, we distinguish between the solver's way of representing
  // them. it can be either binary, hex, or decimal.
  if (sort->get_sort_kind() == BV)
  {
    if (value.substr(0, 2) == "#b")
    {
      // bianry representation
      resulting_term = make_value(value.substr(2, value.size() - 2), sort, 2);
    }
    else if (value.substr(0, 2) == "#x")
    {
      // hex representation
      resulting_term = make_value(value.substr(2, value.size() - 2), sort, 16);
    }
    else
    {
      // decimal representation.
      // parse strings of the form (_ bv<decimal> <bitwidth>)
      size_t index_of__ = value.find("_ ");
      assert(index_of__ != string::npos);
      int start_of_decimal = index_of__ + 4;
      int end_of_decimal = value.find(' ', start_of_decimal);
      string decimal =
          value.substr(start_of_decimal, end_of_decimal - start_of_decimal + 1);
      resulting_term = make_value(decimal, sort, 10);
    }
  }
  else if (sort->get_sort_kind() == BOOL)
  {
    Assert(value == "true" || value == "false");
    bool b = (value == "true");
    resulting_term = make_value(b);
  }
  else
  {
    resulting_term = make_value(value, t->get_sort());
  }
  return resulting_term;
}

string GenericSolver::strip_value_from_result(string result) const
{
  // trim spaces
  result = trim(result);

  // value string ends at first ")" or end of string.
  int end_of_value = result.size() - 1;
  while (result.at(end_of_value) == ')' || result.at(end_of_value) == ' ')
  {
    end_of_value--;
  }

  // value string begins at the first non-space after '('
  int start_of_value = end_of_value;
  while (result.at(start_of_value) != '(')
  {
    start_of_value--;
  }
  while (result.at(start_of_value) != ' ')
  {
    start_of_value++;
  }
  start_of_value++;

  // special case for bit-vectors with smt-lib style
  // (_ bv<value> <bitwidth>)
  // in this case we only take <value>
  if (result.find("bv", start_of_value) == start_of_value)
  {
    start_of_value -= 3;
    end_of_value++;
  }

  // crop the relevant substring
  string strip =
      result.substr(start_of_value, end_of_value - start_of_value + 1);
  return strip;
}

void GenericSolver::get_unsat_assumptions(UnorderedTermSet & out)
{
  // run get-unsat-assumptions command
  string result = run_command("(" + GET_UNSAT_ASSUMPTIONS_STR + ")", false);

  // check that there was no error
  check_no_error(result);

  // parse the result -- get the assumptions
  UnorderedTermSet assumptions = get_assumptions_from_string(result);

  // put the result in out
  out.insert(assumptions.begin(), assumptions.end());
}

void GenericSolver::check_no_error(string str) const
{
  str = trim(str);
  string err_prefix("(error ");
  if (str.compare(0, err_prefix.size(), err_prefix) == 0)
  {
    throw SmtException("Exception from the solver: " + str);
  }
}

UnorderedTermSet GenericSolver::get_assumptions_from_string(string result) const
{
  // the result from the solver is a
  // space-separated list of Boolean literals.
  UnorderedTermSet literals;

  // trim the result from spaces
  result = trim(result);

  // unwrap parenthesis and trim spaces again
  string strip = result.substr(1, result.size() - 2);
  strip = trim(strip);

  // position in the string
  int index = 0;
  // if true, current literal is positive.
  // otherwise, it has the form (not <var>)
  bool positive;

  // iterate the string
  while (index < strip.size())
  {
    // beginning and end of literal
    int begin;
    int end;

    // negative literal
    if (strip.substr(index, 5) == "(not ")
    {
      begin = index + 5;
      end = strip.find(")", begin + 1) - 1;
      assert(end != string::npos);
      positive = false;
    }
    else
    {
      // positive literal -- starts with the variable name
      begin = index;
      // end -- one character after the end of the substring
      end = strip.find(" ", begin + 1);
      if (end == string::npos)
      {
        end = strip.size();
      }
      // end -- the actual end of the substring
      end--;
      positive = true;
    }

    // retrieve the literal from the map
    string str_atom = strip.substr(begin, end - begin + 1);
    assert(name_term_map->find(str_atom) != name_term_map->end());
    Term atom = (*name_term_map)[str_atom];
    Term literal;
    if (positive)
    {
      literal = atom;
    }
    else
    {
      literal = make_term(Not, atom);
    }

    // add the literal to the result
    literals.insert(literal);
    if (positive)
    {
      // next beginning is after a space
      index = end + 2;
    }
    else
    {
      // next beginning is after a space and a ')'
      index = end + 3;
    }
  }
  return literals;
}

UnorderedTermMap GenericSolver::get_array_values(const Term & arr,
                                                 Term & out_const_base) const
{
  throw NotImplementedException(
      "Generic solvers do not support get-value for arryas");
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
  string names;
  for (Term t : assumptions)
  {
    // assumptions can only be Boolean literals
    if (t->get_sort()->get_sort_kind() != BOOL)
    {
        throw IncorrectUsageException(
            "Expecting boolean indicator literals but got: " + t->to_string());
    }

    // add the name of the literal to the list of assumptions
    assert(term_name_map->find(t) != term_name_map->end());
    names += " " + (*term_name_map)[t];
  }

  // send command to the solver and parse it
  string result =
      run_command("(" + CHECK_SAT_ASSUMING_STR + " (" + names + "))", false);
  Result r = str_to_result(result);
  return r;
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
