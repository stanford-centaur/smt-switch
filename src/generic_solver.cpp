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

GenericSolver::GenericSolver(string path, vector<string> cmd_line_args, uint write_buf_size, uint read_buf_size, SolverEnum se)
  : AbsSmtSolver(se), path(path), cmd_line_args(cmd_line_args), write_buf_size(write_buf_size), read_buf_size(read_buf_size),
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
  // TODO uncomment when start_solver is implemented
  // start_solver();
}

GenericSolver::~GenericSolver() {
  //deallocate the buffers memory
  delete write_buf;
  delete read_buf;
  delete term_counter;
  // close the solver process
  // TODO uncomment when close_solver is implemented
  // close_solver();
}

void GenericSolver::start_solver() {
  assert(false);
}

void GenericSolver::close_solver() {
  assert(false);
}
 
Sort GenericSolver::make_sort(const Sort & sort_con, const SortVec & sorts) const {
  assert(false);
}

Sort GenericSolver::make_sort(const std::string name, uint64_t arity) const {
  assert(false);
}

Sort GenericSolver::make_sort(const SortKind sk) const
{
  assert(false);
}

Sort GenericSolver::make_sort(const SortKind sk, uint64_t size) const
{
  assert(false);
}

Sort GenericSolver::make_sort(const SortKind sk, const Sort & sort1) const
{
  assert(false);
}

Sort GenericSolver::make_sort(const SortKind sk,
                              const Sort & sort1,
                              const Sort & sort2) const
{
  assert(false);
}

Sort GenericSolver::make_sort(const SortKind sk,
                              const Sort & sort1,
                              const Sort & sort2,
                              const Sort & sort3) const
{
  assert(false);
}

Sort GenericSolver::make_sort(SortKind sk, const SortVec & sorts) const
{
  assert(false);
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
  assert(false);
}

void GenericSolver::set_logic(const std::string logic)
{
  assert(false);
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
