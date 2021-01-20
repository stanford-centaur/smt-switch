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

#include "assert.h"

#include "generic_solver.h"
#include "sort_inference.h"
#include "sort.h"
#include "smtlib_utils.h"
#include "utils.h"


#include<unistd.h>
#include<sys/wait.h>
#include<sys/prctl.h>
#include<signal.h>
#include<stdlib.h>
#include<string.h>
#include<stdio.h>
#include<algorithm>
#include<fcntl.h>
#include <poll.h>

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
GenericSolver::GenericSolver(string path, vector<string> cmd_line_args, uint write_buf_size, uint read_buf_size)
  : AbsSmtSolver(SolverEnum::GENERIC_SOLVER), path(path), cmd_line_args(cmd_line_args), write_buf_size(write_buf_size), read_buf_size(read_buf_size),
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
 
Sort GenericSolver::make_sort(const Sort & sort_con, const SortVec & sorts) const {
  assert(sort_name_map->find(sort_con) != sort_name_map->end());
  assert(sort_con->get_arity() == sorts.size());
  for (Sort sort : sorts)
  {
    assert(sort_name_map->find(sort) != sort_name_map->end());
  }
  Sort sort = make_uninterpreted_generic_sort(sort_con, sorts);
  string name = sort->get_uninterpreted_name();
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
  if (name_sort_map->find(name) == name_sort_map->end())
  {
    Sort sort = make_uninterpreted_generic_sort(name, arity);
    (*name_sort_map)[name] = sort;
    (*sort_name_map)[sort] = name;
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
  Sort sort = make_generic_sort(sk);
  string name = sort->to_string();
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
  Sort sort = make_generic_sort(sk, size);
  string name = sort->to_string();
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
  Sort sort = make_generic_sort(sk, sorts);
  string name = sort->to_string();
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

Term GenericSolver::make_term(bool b) const
{
  assert(false);
}

Term GenericSolver::make_term(int64_t i, const Sort & sort) const
{
  assert(false);
}

Term GenericSolver::make_term(const string name,
                              const Sort & sort,
                              uint64_t base) const
{
  assert(false);
}

Term GenericSolver::make_term(const Term & val, const Sort & sort) const
{
  assert(false);
}

Term GenericSolver::make_symbol(const string name, const Sort & sort)
{
  assert(false);
}

Term GenericSolver::make_param(const string name, const Sort & sort)
{
  assert(false);
}

Term GenericSolver::make_term(const Op op, const Term & t) const
{
  assert(false);
}

Term GenericSolver::make_term(const Op op,
                              const Term & t1,
                              const Term & t2) const
{
  assert(false);
}

Term GenericSolver::make_term(const Op op,
                              const Term & t1,
                              const Term & t2,
                              const Term & t3) const
{
  assert(false);
}

Term GenericSolver::make_term(const Op op, const TermVec & terms) const
{
  assert(false);
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
  assert(false);
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
  assert(false);
}

Result GenericSolver::check_sat()
{
  assert(false);
}

Result GenericSolver::check_sat_assuming(const TermVec & assumptions)
{
  assert(false);
}

void GenericSolver::push(uint64_t num)
  {
    assert(false);
  }

void GenericSolver::pop(uint64_t num)
{
  assert(false);
}

void GenericSolver::reset_assertions()
  {
    assert(false);
  }

}  // namespace smt

#endif // __APPLE__
