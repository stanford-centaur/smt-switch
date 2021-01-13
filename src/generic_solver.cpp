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

  //start the process with the solver binary
  start_solver();
}

GenericSolver::~GenericSolver() {
  //deallocate the buffers memory
  delete write_buf;
  delete read_buf;
  delete term_counter;
  //deallocate maps
  delete name_sort_map;
  delete sort_name_map;
  delete name_term_map;
  delete term_name_map;
  //close the solver process
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

    //ask kernel to deliver SIGTERM in case the parent dies
    prctl(PR_SET_PDEATHSIG, SIGTERM);
    // The following part is based on: https://stackoverflow.com/a/5797901/1364765
    // The execv command expects an array, and so we create one.
    // First element is the program name, last element is NULL, and in between are
    // the elements of cmd_line_args, casted to (char*) from std::string.
    // Here we identify the program name with its path.
    const char **argv = new const char* [cmd_line_args.size()+2];  
    argv[0] = path.c_str();     
    for (int i = 1;  i <= cmd_line_args.size();  i++) {
            argv[i] = cmd_line_args[i-1].c_str();
    }
    argv[cmd_line_args.size() + 1] = NULL;    
    execv (path.c_str(), (char **)argv);
    // Nothing below this line should be executed by child process. If so, 
    // it means that the execl function wasn't successfull, so lets exit:
    // TODO should we free the memory of argv?
    assert(false);
    exit(1);
  }
  //close unused pipe ends
  close(outpipefd[0]);
  close(inpipefd[1]);
  // TODO uncomment when set_opt is implemented
  // set_opt("print-success", "true");
}

void GenericSolver::close_solver() {
  kill(pid, SIGKILL); //send SIGKILL signal to the child process
  waitpid(pid, &status, 0); 
}
}  // namespace smt
