/*********************                                                        */
/*! \file portfolio_solver.cpp
** \verbatim
** Top contributors (to current version):
**   Amalee Wilson
** This file is part of the smt-switch project.
** Copyright (c) 2021 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Implementation of a portfolio solving function that takes a vector
**        of solvers and a term, and returns check_sat from the first solver
**        that finishes.
**/

#include "portfolio_solver.h"

#include <poll.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#include <cerrno>
#include <csignal>
#include <cstdio>
#include <cstring>
#include <exception>
#include <iostream>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#include "exceptions.h"
#include "smt_defs.h"
#include "solver.h"
#include "solver_enums.h"
#include "sort.h"
#include "term_translator.h"

namespace {

using smt::Result;
using smt::ResultType;
using smt::SmtSolver;
using smt::Term;

// What a child writes before closing its pipe: this tag, then for an answer
// the ResultType as one byte, and the explanation or error message.
constexpr char answer_tag = 'a';
constexpr char error_tag = 'e';

// Writes all of data to fd, as far as the pipe lets it.
void write_all(int fd, const std::string & data)
{
  const char * next = data.data();
  std::size_t left = data.size();
  while (left > 0)
  {
    ssize_t written = write(fd, next, left);
    if (written < 0)
    {
      if (errno == EINTR)
      {
        continue;
      }
      return;
    }
    next += written;
    left -= static_cast<std::size_t>(written);
  }
}

// Runs in a child: solves term with solver and reports on fd. Never returns.
[[noreturn]] void solve_and_report(SmtSolver solver, Term term, int fd)
{
  std::string report;
  try
  {
    smt::TermTranslator to_solver(solver);
    solver->assert_formula(to_solver.transfer_term(term, smt::BOOL));
    Result result = solver->check_sat();
    report = answer_tag;
    report += static_cast<char>(result.result);
    report += result.explanation;
  }
  catch (const std::exception & e)
  {
    report = error_tag;
    report += e.what();
  }
  catch (...)
  {
    report = error_tag;
    report += "unknown exception";
  }
  write_all(fd, report);
  // Not exit(): the caller's exit handlers and static destructors, and any
  // output it had buffered, belong to the parent.
  _exit(0);
}

struct Child
{
  Child(pid_t pid, int fd, std::string label)
      : pid(pid), fd(fd), label(std::move(label))
  {
  }

  pid_t pid;
  int fd;
  std::string label;
  std::string report;
  bool reaped = false;
  int status = 0;
};

// The children of one portfolio_solve call. Kills and reaps every one of
// them however the call ends, so that none outlives it.
class Children
{
 public:
  Children() = default;
  Children(const Children &) = delete;
  Children & operator=(const Children &) = delete;
  ~Children() { kill_and_reap(); }

  void add(Child child) { children_.push_back(std::move(child)); }
  std::vector<Child> & all() { return children_; }

  void kill_and_reap()
  {
    // Each child leads its own process group, so this also ends whatever it
    // started itself, such as the generic solver's binary.
    for (const Child & child : children_)
    {
      if (!child.reaped)
      {
        kill(-child.pid, SIGKILL);
      }
    }
    for (Child & child : children_)
    {
      if (child.fd >= 0)
      {
        close(child.fd);
        child.fd = -1;
      }
      while (!child.reaped)
      {
        if (waitpid(child.pid, &child.status, 0) >= 0 || errno != EINTR)
        {
          child.reaped = true;
        }
      }
    }
  }

 private:
  std::vector<Child> children_;
};

// Why a child gave no answer, once it has been reaped.
std::string failure(const Child & child)
{
  std::string reason;
  if (!child.report.empty() && child.report[0] == error_tag)
  {
    reason = child.report.substr(1);
  }
  else if (WIFSIGNALED(child.status))
  {
    reason = "terminated by signal " + std::to_string(WTERMSIG(child.status))
             + " (" + strsignal(WTERMSIG(child.status)) + ")";
  }
  else
  {
    reason = "exited without an answer";
  }
  return child.label + ": " + reason;
}

}  // namespace

namespace smt {

PortfolioSolver::PortfolioSolver(std::vector<SmtSolver> slvrs, Term trm)
    : solvers(slvrs), portfolio_term(trm)
{
}

Result PortfolioSolver::portfolio_solve()
{
  // Otherwise each child would inherit, and later print, a copy of anything
  // the caller has buffered.
  std::cout.flush();
  std::cerr.flush();
  std::fflush(nullptr);

  Children children;
  for (const SmtSolver & solver : solvers)
  {
    int fds[2];
    if (pipe(fds) != 0)
    {
      throw SmtException(std::string("Could not create a pipe for a solver: ")
                         + std::strerror(errno));
    }
    pid_t pid = fork();
    if (pid < 0)
    {
      const int error = errno;
      close(fds[0]);
      close(fds[1]);
      throw SmtException(std::string("Could not start a solver process: ")
                         + std::strerror(error));
    }
    if (pid == 0)
    {
      setpgid(0, 0);
      close(fds[0]);
      solve_and_report(solver, portfolio_term, fds[1]);
    }
    // Also here, so that the group exists even if the child has not run yet.
    setpgid(pid, pid);
    close(fds[1]);
    std::ostringstream label;
    label << solver->get_solver_enum();
    children.add(Child(pid, fds[0], label.str()));
  }

  // Read the reports as they come; a child's pipe closes when it exits.
  std::size_t running = children.all().size();
  while (running > 0)
  {
    std::vector<pollfd> polled;
    std::vector<Child *> polled_children;
    for (Child & child : children.all())
    {
      if (child.fd >= 0)
      {
        polled.push_back({ child.fd, POLLIN, 0 });
        polled_children.push_back(&child);
      }
    }
    if (poll(polled.data(), polled.size(), -1) < 0)
    {
      if (errno == EINTR)
      {
        continue;
      }
      throw SmtException(std::string("Could not wait for the solvers: ")
                         + std::strerror(errno));
    }
    for (std::size_t i = 0; i < polled.size(); ++i)
    {
      if (polled[i].revents == 0)
      {
        continue;
      }
      Child & child = *polled_children[i];
      char buffer[4096];
      ssize_t got = read(child.fd, buffer, sizeof buffer);
      if (got < 0 && errno == EINTR)
      {
        continue;
      }
      if (got > 0)
      {
        child.report.append(buffer, static_cast<std::size_t>(got));
        continue;
      }
      // The child is done, with or without a report.
      close(child.fd);
      child.fd = -1;
      --running;
      if (child.report.size() >= 2 && child.report[0] == answer_tag)
      {
        return Result(static_cast<ResultType>(child.report[1]),
                      child.report.substr(2));
      }
    }
  }

  // No child answered; reap them all to say why.
  children.kill_and_reap();
  std::string message = "No solver in the portfolio gave an answer:";
  for (const Child & child : children.all())
  {
    message += "\n  " + failure(child);
  }
  throw SmtException(message);
}

}  // namespace smt
