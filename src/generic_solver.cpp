/*!
 * \file generic_solver.cpp
 * \brief A class that represents a generic solver
 * \author Yoni Zohar
 * \author Áron Ricardo Perez-Lopez
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
/* Uses code to interact with a process from:
** https://stackoverflow.com/a/6172578/1364765
*/

#include "smt-switch/generic_solver.h"

#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#ifdef __linux__
#include <sys/prctl.h>
#endif
#include <sys/wait.h>
#include <unistd.h>

#include <algorithm>
#include <cerrno>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <exception>
#include <fstream>
#include <iterator>
#include <limits>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <type_traits>
#include <unordered_set>
#include <utility>
#include <vector>

#include "smt-switch/datatype.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/generic_datatype.h"
#include "smt-switch/generic_sort.h"
#include "smt-switch/generic_term.h"
#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/solver_utils.h"
#include "smt-switch/sort.h"
#include "smt-switch/sort_inference.h"
#include "smt-switch/term.h"
#include "smt-switch/utils.h"

namespace smt {

/** The standard options that SMT-LIB 2.6, Section 4.1.7, permits only in
 * start mode.
 */
constexpr std::string_view start_only_options[] = {
  "global-declarations",       "interactive-mode",    "produce-assertions",
  "produce-assignments",       "produce-models",      "produce-proofs",
  "produce-unsat-assumptions", "produce-unsat-cores", "random-seed",
};

/** An SMT-LIB command, e.g. (push 1)
 * @param name the command's name
 * @param args its arguments, each written after a space
 */
template <class... Args>
static std::string smtlib_command(std::string_view name, const Args &... args)
{
  // std::string's += takes a char, so an integer would be appended as one
  static_assert((std::is_convertible_v<const Args &, std::string_view> && ...),
                "each argument must be text");
  std::string command = "(";
  command += name;
  ((command += ' ', command += args), ...);
  command += ')';
  return command;
}

template <class... Args>
bool GenericSolver::send_or_hold(std::string_view name,
                                 const Args &... args) const
{
  return send_or_hold(smtlib_command(name, args...));
}

template <class... Args>
std::string GenericSolver::run_command(CommandKind kind,
                                       std::string_view name,
                                       const Args &... args) const
{
  return run_command(smtlib_command(name, args...), kind);
}

// helper functions
static bool is_white_space(char c)
{
  return (c == ' ' || c == '\t' || c == '\n' || c == '\r');
}

// Close a descriptor and mark it unset: teardown can run twice, and a
// second close would land on whatever the kernel has since reused the
// number for. EINTR is not retried, the descriptor being gone by then.
static void close_fd(int & fd)
{
  if (fd < 0)
  {
    return;
  }
  close(fd);
  fd = -1;
}

// Whether a trimmed response is the binary reporting an error.
static bool is_error_response(const std::string & response)
{
  const std::string err_prefix("(error ");
  return response.compare(0, err_prefix.size(), err_prefix) == 0;
}

/** The offset just past the s-expression that starts at `i` in `buf`, where
 * `buf[i]` is not whitespace, or std::string::npos if `buf` holds no whole
 * one from there on.
 *
 * An s-expression is a bare atom (`sat`, `#b01`) or a parenthesised list.
 * Parentheses cannot simply be counted, since string literals ("..."),
 * quoted symbols (|...|) and comments (;...) may hold unmatched ones -- an
 * error message quoting a stray ')' back at us is the obvious way to meet
 * that.
 */
static std::size_t sexpr_end(const std::string & buf, std::size_t i)
{
  if (buf[i] == '|')
  {
    // a quoted symbol, which may hold spaces and parentheses
    i = buf.find('|', i + 1);
    return i == std::string::npos ? std::string::npos : i + 1;
  }

  if (buf[i] != '(')
  {
    // an atom is only known to have ended once a delimiter turns up
    while (i < buf.size() && !is_white_space(buf[i]) && buf[i] != '('
           && buf[i] != ')' && buf[i] != ';')
    {
      i++;
    }
    return (i < buf.size()) ? i : std::string::npos;
  }

  int depth = 0;
  while (i < buf.size())
  {
    if (buf[i] == ';')
    {
      while (i < buf.size() && buf[i] != '\n')
      {
        i++;
      }
    }
    else if (buf[i] == '|')
    {
      i = buf.find('|', i + 1);
      if (i == std::string::npos)
      {
        return std::string::npos;
      }
      i++;
    }
    else if (buf[i] == '"')
    {
      i++;
      while (true)
      {
        i = buf.find('"', i);
        if (i == std::string::npos)
        {
          return std::string::npos;
        }
        i++;
        // a doubled quote is SMT-LIB's escape, so the literal runs on
        if (i == buf.size())
        {
          return std::string::npos;
        }
        if (buf[i] != '"')
        {
          break;
        }
        i++;
      }
    }
    else
    {
      if (buf[i] == '(')
      {
        depth++;
      }
      else if (buf[i] == ')')
      {
        depth--;
        if (depth == 0)
        {
          return i + 1;
        }
      }
      i++;
    }
  }
  return std::string::npos;
}

/**
 * The top-level subexpressions of a parenthesized s-expression, so that
 * "(store a #b01 #b10)" gives { "store", "a", "#b01", "#b10" }, and "()"
 * gives an empty vector. Returns no value for anything that is not one
 * parenthesized expression, such as an atom.
 */
static std::optional<std::vector<std::string>> split_sexpr(
    const std::string & s)
{
  if (s.empty() || s.front() != '(' || sexpr_end(s, 0) != s.size())
  {
    return std::nullopt;
  }

  std::vector<std::string> parts;
  const std::size_t last = s.size() - 1;
  std::size_t i = 1;
  while (i < last)
  {
    if (is_white_space(s[i]))
    {
      i++;
      continue;
    }
    // the closing parenthesis delimits the last subexpression, so every one
    // of them ends inside `s`
    const std::size_t end = sexpr_end(s, i);
    if (end == std::string::npos || end <= i)
    {
      return std::nullopt;
    }
    parts.push_back(s.substr(i, end - i));
    i = end;
  }
  return parts;
}

/** Length of the first complete response in `buf`, including any leading
 * whitespace, or std::string::npos if `buf` does not hold a whole one
 * yet. Exactness matters: over- or under-reading by a byte slips the
 * command and response streams out of step for good.
 */
static std::size_t response_length(const std::string & buf)
{
  std::size_t i = 0;
  while (i < buf.size() && is_white_space(buf[i]))
  {
    i++;
  }
  if (i == buf.size())
  {
    return std::string::npos;
  }
  return sexpr_end(buf, i);
}

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

const std::chrono::milliseconds GenericSolver::default_response_timeout =
    std::chrono::hours(1);
const std::chrono::milliseconds GenericSolver::no_response_timeout =
    std::chrono::milliseconds(-1);

// class methods implementation
GenericSolver::GenericSolver(std::string solver_path,
                             std::vector<std::string> args,
                             std::chrono::milliseconds timeout,
                             unsigned int buffer_size)
    : AbsSmtSolver(SolverEnum::GENERIC_SOLVER),
      path(std::move(solver_path)),
      cmd_line_args(std::move(args)),
      read_buf_size(buffer_size),
      response_timeout(timeout)
{
  // Buffer sizes over 256 caused issues in tests.
  // Until this is investigated, we support a conservative
  // limit of 256.
  // Similarly for buffers of size 1.
  if (buffer_size < 2 || buffer_size > 256)
  {
    std::string msg(
        "Generic Solvers require a buffer size of at least 2 and at most 256.");
    throw IncorrectUsageException(msg);
  }
  read_buf.resize(buffer_size);
  // start the process with the solver binary
  try
  {
    start_solver();
  }
  catch (...)
  {
    // a throwing constructor gets no destructor, so clean up here; catch
    // everything, as a slow solver leaves by InternalSolverException
    close_solver();
    throw;
  }
}

GenericSolver::~GenericSolver()
{
  // close the solver process
  close_solver();
}

void GenericSolver::start_solver()
{
  launch_binary();
  set_opt("print-success", "true");
  set_opt("global-declarations", "true");
}

void GenericSolver::launch_binary() const
{
  // execv's arguments, the program first and a null last, made before the
  // fork: the child must not allocate, as another thread may hold the
  // allocator's lock at the fork, which the child would never see released
  std::vector<char *> argv;
  argv.reserve(cmd_line_args.size() + 2);
  argv.push_back(const_cast<char *>(path.c_str()));
  for (const std::string & arg : cmd_line_args)
  {
    argv.push_back(const_cast<char *>(arg.c_str()));
  }
  argv.push_back(nullptr);

  // Any exec closes every end, so that another child's program, such as a
  // second solver's binary, cannot hold this solver's pipes open.
  if (int pipe_errno = detail::make_cloexec_pipe(inpipefd); pipe_errno != 0)
  {
    throw InternalSolverException(
        "Failed to create a pipe from the solver binary at " + path + ": "
        + strerror(pipe_errno));
  }
  if (int pipe_errno = detail::make_cloexec_pipe(outpipefd); pipe_errno != 0)
  {
    close_fd(inpipefd[0]);
    close_fd(inpipefd[1]);
    throw InternalSolverException(
        "Failed to create a pipe to the solver binary at " + path + ": "
        + strerror(pipe_errno));
  }
  // a third pipe tells the parent how execv() went: a successful exec
  // closes the write end, so end-of-file means started, an errno means not
  int execpipefd[2] = { -1, -1 };
  if (int pipe_errno = detail::make_cloexec_pipe(execpipefd); pipe_errno != 0)
  {
    close_fd(inpipefd[0]);
    close_fd(inpipefd[1]);
    close_fd(outpipefd[0]);
    close_fd(outpipefd[1]);
    throw InternalSolverException(
        "Failed to create a startup pipe for the solver binary at " + path
        + ": " + strerror(pipe_errno));
  }
  pid = fork();
  if (pid < 0)
  {
    int fork_errno = errno;
    close_fd(inpipefd[0]);
    close_fd(inpipefd[1]);
    close_fd(outpipefd[0]);
    close_fd(outpipefd[1]);
    close_fd(execpipefd[0]);
    close_fd(execpipefd[1]);
    throw InternalSolverException("Failed to start the solver binary at " + path
                                  + ": " + strerror(fork_errno));
  }
  if (pid == 0)
  {
    // Child
    dup2(outpipefd[0], STDIN_FILENO);
    dup2(inpipefd[1], STDOUT_FILENO);
    // dup2() clears the flag on the copy it makes, but leaves an end that
    // already was stdin or stdout as it was, which exec would then close.
    fcntl(STDIN_FILENO, F_SETFD, 0);
    fcntl(STDOUT_FILENO, F_SETFD, 0);
    // stderr stays the parent's: everything on the pipe is read as an
    // answer, and SMT-LIB answers, errors included, all come on stdout

    // drop the spare copies before the exec: a solver still holding the
    // write end of its own stdin never sees the EOF close_solver() sends
    // it. An end dup2() copied onto itself is a stream, so only forget it.
    for (int * fd :
         { &outpipefd[0], &outpipefd[1], &inpipefd[0], &inpipefd[1] })
    {
      if (*fd > STDERR_FILENO)
      {
        close_fd(*fd);
      }
      else
      {
        *fd = -1;
      }
    }
    // the startup pipe is exempt: its write end has to outlive the exec,
    // which closes it through FD_CLOEXEC only if it succeeds
    close_fd(execpipefd[0]);

#ifdef __linux__
    // ask kernel to deliver SIGTERM in case the parent dies; other
    // systems have no such request, so there the child is not signalled
    prctl(PR_SET_PDEATHSIG, SIGTERM);
#endif
    //    fcntl(inpipefd[1], F_SETFL, O_NONBLOCK);
    execv(path.c_str(), argv.data());
    // this is a forked copy of the parent, so it must not throw: report
    // the errno and _exit(), exit() flushing its stdio into the pipe
    int exec_errno = errno;
    const char * reason = reinterpret_cast<const char *>(&exec_errno);
    size_t left = sizeof(exec_errno);
    while (left > 0)
    {
      ssize_t just_written = write(execpipefd[1], reason, left);
      if (just_written < 0)
      {
        if (errno == EINTR)
        {
          continue;
        }
        // the parent still sees a short read, and still reports a failure
        break;
      }
      reason += just_written;
      left -= just_written;
    }
    _exit(EXIT_FAILURE);
  }
  // close unused pipe ends
  close_fd(outpipefd[0]);
  close_fd(inpipefd[1]);
  // the read below only sees end-of-file once no one holds the write end
  close_fd(execpipefd[1]);
  // no deadline needed: the child gets to execv() within a few syscalls
  int exec_errno = 0;
  ssize_t reported;
  do
  {
    reported = read(execpipefd[0], &exec_errno, sizeof(exec_errno));
  } while (reported < 0 && errno == EINTR);
  int read_errno = errno;
  close_fd(execpipefd[0]);
  if (reported != 0)
  {
    std::string reason;
    if (reported == static_cast<ssize_t>(sizeof(exec_errno)))
    {
      reason = strerror(exec_errno);
    }
    else if (reported < 0)
    {
      reason = std::string("could not be determined: ") + strerror(read_errno);
    }
    else
    {
      reason = "could not be determined: the process died before reporting it";
    }
    // the child and the pipes are left to the caller's close_solver()
    throw IncorrectUsageException("failure to run binary: " + path + ": "
                                  + reason);
  }
}

void GenericSolver::write_internal(std::string str) const
{
  // MathSAT intermittently drops a character -- in practice the closing
  // parenthesis -- out of a command that reaches it one byte at a time,
  // and then waits for the rest of a command it already has, so hand the
  // command over in as few write() calls as the pipe allows.
  //
  // Writing to a binary that has exited or closed its input raises
  // SIGPIPE, which kills the whole process unless it is handled. Blocking
  // it in this thread makes write() fail with EPIPE instead, and leaves the
  // signal handling of the program using the library alone.
  sigset_t sigpipe_set;
  sigemptyset(&sigpipe_set);
  sigaddset(&sigpipe_set, SIGPIPE);
  // a SIGPIPE can only be pending here if the caller already blocks it,
  // and then it is the caller's, not one of ours to discard
  sigset_t pending;
  sigpending(&pending);
  bool sigpipe_was_pending = sigismember(&pending, SIGPIPE);
  sigset_t old_mask;
  pthread_sigmask(SIG_BLOCK, &sigpipe_set, &old_mask);

  int write_errno = 0;
  std::string::size_type written_chars = 0;
  while (written_chars < str.size())
  {
    ssize_t just_written = write(
        outpipefd[1], str.data() + written_chars, str.size() - written_chars);
    if (just_written < 0)
    {
      if (errno == EINTR)
      {
        continue;
      }
      write_errno = errno;
      break;
    }
    written_chars += just_written;
  }

  if (write_errno == EPIPE && !sigpipe_was_pending)
  {
    // discard the SIGPIPE the failed write raised, which unblocking would
    // otherwise deliver; sigwait() blocks until one is pending, so only
    // call it once sigpending() has found one
    sigpending(&pending);
    if (sigismember(&pending, SIGPIPE))
    {
      int discarded;
      sigwait(&sigpipe_set, &discarded);
    }
  }
  pthread_sigmask(SIG_SETMASK, &old_mask, nullptr);
  if (write_errno == EPIPE)
  {
    binary_exited_ = true;
  }
  if (write_errno != 0)
  {
    throw InternalSolverException(
        "Failed to send a command to the solver binary at " + path + ": "
        + strerror(write_errno));
  }
}

bool GenericSolver::take_response(std::string & response) const
{
  std::string::size_type length = response_length(response_buffer);
  if (length == std::string::npos)
  {
    return false;
  }
  response = response_buffer.substr(0, length);
  response_buffer.erase(0, length);
  return true;
}

void GenericSolver::await_response(
    const std::chrono::steady_clock::time_point & deadline,
    const std::string & cmd) const
{
  while (true)
  {
    // -1 makes poll() wait forever, which is what no deadline asks for
    int timeout_ms = -1;
    if (deadline != std::chrono::steady_clock::time_point::max())
    {
      auto left = std::chrono::duration_cast<std::chrono::milliseconds>(
                      deadline - std::chrono::steady_clock::now())
                      .count();
      if (left <= 0)
      {
        throw InternalSolverException("The solver binary at " + path
                                      + " did not respond within "
                                      + std::to_string(response_timeout.count())
                                      + " ms to the command: " + cmd);
      }
      // poll() takes an int, so a distant deadline is waited out in slices
      timeout_ms = detail::fits_in<int>(left) ? static_cast<int>(left)
                                              : std::numeric_limits<int>::max();
    }
    struct pollfd pfd;
    pfd.fd = inpipefd[0];
    pfd.events = POLLIN;
    pfd.revents = 0;
    int ready = poll(&pfd, 1, timeout_ms);
    if (ready > 0)
    {
      return;
    }
    // a finished slice or an interrupted wait just retries the loop
    if (ready < 0 && errno != EINTR)
    {
      int poll_errno = errno;
      throw InternalSolverException("Failed to wait for the solver binary at "
                                    + path
                                    + " to respond: " + strerror(poll_errno));
    }
  }
}

std::string GenericSolver::read_internal(const std::string & cmd) const
{
  std::chrono::steady_clock::time_point deadline =
      std::chrono::steady_clock::time_point::max();
  if (response_timeout >= std::chrono::milliseconds::zero())
  {
    // A timeout past what the clock can count stays at its last moment, as
    // adding it would overflow.
    std::chrono::steady_clock::time_point now =
        std::chrono::steady_clock::now();
    if (response_timeout
        < std::chrono::duration_cast<std::chrono::milliseconds>(deadline - now))
    {
      deadline = now + response_timeout;
    }
  }
  std::string result;
  while (!take_response(result))
  {
    await_response(deadline, cmd);
    ssize_t just_read = read(inpipefd[0], read_buf.data(), read_buf_size);
    if (just_read < 0)
    {
      if (errno == EINTR)
      {
        continue;
      }
      int read_errno = errno;
      throw InternalSolverException(
          "Failed to read a response from the solver binary at " + path + ": "
          + strerror(read_errno));
    }
    if (just_read == 0)
    {
      // the solver is gone, so what arrived is all there will ever be
      binary_exited_ = true;
      if (response_buffer.empty())
      {
        throw InternalSolverException(
            "The solver binary at " + path
            + " exited without responding to the command: " + cmd);
      }
      result = response_buffer;
      response_buffer.clear();
      break;
    }
    response_buffer.append(read_buf.data(), just_read);
  }
  // normalize output of solver:
  // - no newlines in the middle of the content
  // - no double spaces
  while (result.find("\n") != std::string::npos)
  {
    result.replace(result.find("\n"), 1, " ");
  }
  while (result.find("  ") != std::string::npos)
  {
    result.replace(result.find("  "), 2, " ");
  }
  return result;
}

std::string GenericSolver::exchange(const std::string & cmd) const
{
  // send the cmd string, with a newline to simulate an "enter" hit
  write_internal(cmd + "\n");
  std::string result = read_internal(cmd);
  return trim(result);
}

std::string GenericSolver::send_command(const std::string & cmd) const
{
  std::string result;
  try
  {
    result = exchange(cmd);
  }
  catch (InternalSolverException &)
  {
    // a binary that died of the command took the solver's state with it,
    // and one still busy past the deadline would answer it in place of the
    // next command
    restart_binary();
    throw;
  }
  if (binary_exited_ || is_error_response(result))
  {
    restore_binary();
  }
  return result;
}

void GenericSolver::restore_binary() const
{
  // SMT-LIB gives a command that fails no effect, so a binary that still
  // answers is in the state it was in before the command
  if (!binary_exited_)
  {
    try
    {
      exchange("(get-info :name)");
      if (!binary_exited_)
      {
        return;
      }
    }
    catch (InternalSolverException &)
    {
    }
  }
  restart_binary();
}

void GenericSolver::restart_binary() const
{
  // a fresh binary given everything the old one accepted is in that state
  // too, but for the model, as no check-sat is sent again
  try
  {
    close_solver();
    response_buffer.clear();
    binary_exited_ = false;
    launch_binary();
    for (const std::string & cmd : accepted_commands_)
    {
      std::string result = exchange(cmd);
      if (result != "success")
      {
        throw InternalSolverException("it answered " + result + " to " + cmd);
      }
    }
  }
  catch (SmtException & e)
  {
    throw InternalSolverException("Could not restart the solver binary at "
                                  + path + ": " + e.what());
  }
  if (mode_ == SmtLibMode::SAT || mode_ == SmtLibMode::UNSAT)
  {
    mode_ = SmtLibMode::ASSERT;
  }
}

std::string to_string(SmtLibMode mode)
{
  // no default, so that -Wswitch reports an enumerator without a case
  switch (mode)
  {
    case SmtLibMode::START: return "start";
    case SmtLibMode::ASSERT: return "assert";
    case SmtLibMode::SAT: return "sat";
    case SmtLibMode::UNSAT: return "unsat";
  }
  throw NotImplementedException("Unknown SmtLibMode: "
                                + std::to_string(static_cast<int>(mode)));
}

void GenericSolver::require_mode(SmtLibMode needed,
                                 const std::string & operation,
                                 const std::string & reason) const
{
  if (mode_ != needed)
  {
    throw IncorrectUsageException(
        operation + " needs " + to_string(needed) + " mode (" + reason
        + "), but the solver is in " + to_string(mode_) + " mode");
  }
}

std::string GenericSolver::run_command(const std::string & cmd,
                                       CommandKind kind) const
{
  // no default, so that -Wswitch reports an enumerator without a case
  switch (kind)
  {
    case CommandKind::LOGIC:
    case CommandKind::RESET_ASSERTIONS:
    case CommandKind::ASSERTION:
    case CommandKind::CHECK: send_pending_commands(); break;
    case CommandKind::OPTION:
    case CommandKind::RESET:
    case CommandKind::GET: break;
  }
  std::string reply = send_command(cmd);
  // SMT-LIB permits neither kind before set-logic, which callers of the
  // other backends never need. Most binaries go ahead anyway, and cvc5
  // picks ALL itself, but Yices2 knows no theory at all without one, and
  // its refusals do not always say so. Whether or not the binary takes
  // ALL, it is past the start mode afterwards, so it is tried once.
  if ((kind == CommandKind::ASSERTION || kind == CommandKind::CHECK)
      && mode_ == SmtLibMode::START && is_error_response(reply))
  {
    mode_ = SmtLibMode::ASSERT;
    bool all_set = false;
    try
    {
      run_command(CommandKind::LOGIC, SET_LOGIC_STR, "ALL");
      all_set = true;
    }
    catch (SmtException &)
    {
      // the command's own error is the one to report
    }
    if (all_set)
    {
      reply = send_command(cmd);
    }
  }
  switch (kind)
  {
    case CommandKind::OPTION:
    case CommandKind::LOGIC:
    case CommandKind::RESET:
    case CommandKind::RESET_ASSERTIONS:
    case CommandKind::ASSERTION:
      // SMT-LIB has a binary answer this to an option or a logic it does not
      // support.
      if ((kind == CommandKind::OPTION || kind == CommandKind::LOGIC)
          && reply == "unsupported")
      {
        throw NotImplementedException(
            "The solver does not support the "
            "command "
            + cmd);
      }
      if (reply != "success")
      {
        throw IncorrectUsageException(
            "The command did not end with a success message from the solver. "
            "The result was: "
            + reply);
      }
      accepted_commands_.push_back(cmd);
      break;
    case CommandKind::CHECK: break;
    case CommandKind::GET:
      // print-success does not cover a command that answers with a result
      if (is_error_response(reply))
      {
        throw SmtException("Exception from the solver: " + reply);
      }
      break;
  }
  switch (kind)
  {
    case CommandKind::LOGIC:
    case CommandKind::ASSERTION: mode_ = SmtLibMode::ASSERT; break;
    case CommandKind::RESET: mode_ = SmtLibMode::START; break;
    case CommandKind::RESET_ASSERTIONS:
      if (mode_ != SmtLibMode::START)
      {
        mode_ = SmtLibMode::ASSERT;
      }
      break;
    case CommandKind::CHECK:
      // sat and unknown both leave a model to read (SMT-LIB 2.6 Section
      // 4.2.5)
      mode_ =
          str_to_result(reply).is_unsat() ? SmtLibMode::UNSAT : SmtLibMode::SAT;
      break;
    case CommandKind::OPTION:
    case CommandKind::GET: break;
  }
  return reply;
}

void GenericSolver::send_pending_commands() const
{
  // taken off the list first, so a failure part way does not leave the
  // ones already sent to be sent again
  std::vector<std::string> pending;
  pending.swap(pending_commands_);
  pending_definitions_.clear();
  pending_symbols_.clear();
  pending_sort_names_.clear();
  // the terms of the ones after a failure are already made, and need not
  // use the term that failed, so those are sent too
  std::exception_ptr first_failure;
  for (const std::string & cmd : pending)
  {
    try
    {
      run_command(cmd, CommandKind::ASSERTION);
    }
    catch (SmtException &)
    {
      if (!first_failure)
      {
        first_failure = std::current_exception();
      }
    }
  }
  if (first_failure)
  {
    std::rethrow_exception(first_failure);
  }
}

bool GenericSolver::send_or_hold(const std::string & cmd) const
{
  if (mode_ == SmtLibMode::SAT || mode_ == SmtLibMode::UNSAT)
  {
    pending_commands_.push_back(cmd);
    return true;
  }
  run_command(cmd, CommandKind::ASSERTION);
  return false;
}

bool GenericSolver::uses_held_back_sort(const Sort & sort) const
{
  if (pending_sort_names_.empty())
  {
    return false;
  }
  switch (sort->get_sort_kind())
  {
    case ARRAY:
      return uses_held_back_sort(sort->get_indexsort())
             || uses_held_back_sort(sort->get_elemsort());
    case FUNCTION:
      for (const Sort & d : sort->get_domain_sorts())
      {
        if (uses_held_back_sort(d))
        {
          return true;
        }
      }
      return uses_held_back_sort(sort->get_codomain_sort());
    case UNINTERPRETED:
    case UNINTERPRETED_CONS:
      // an applied constructor keeps the constructor's name
      if (pending_sort_names_.find(sort->get_uninterpreted_name())
          != pending_sort_names_.end())
      {
        return true;
      }
      for (const Sort & p : sort->get_uninterpreted_param_sorts())
      {
        if (uses_held_back_sort(p))
        {
          return true;
        }
      }
      return false;
    case DATATYPE:
      // a datatype whose selectors use a held-back sort is declared after
      // it, so is held back itself
      return pending_sort_names_.find(sort->to_string())
             != pending_sort_names_.end();
    // an application of a datatype component has the datatype's sort, or
    // takes a term of it, so the term or its child is what is caught
    case CONSTRUCTOR:
    case SELECTOR:
    case TESTER:
    case BOOL:
    case BV:
    case INT:
    case REAL:
    case STRING: return false;
    case NUM_SORT_KINDS: break;
  }
  return false;
}

std::string GenericSolver::query_text(const Term & term,
                                      const std::string & operation) const
{
  std::string name = term_name(term);
  if (pending_commands_.empty())
  {
    return name;
  }

  // Collect the held-back definitions `term` depends on, each after the
  // ones it uses. A term the binary already has a name for needs nothing
  // underneath it; a term with bound variables has no definition of its
  // own, but its text can name held-back ones.
  TermVec used;
  UnorderedTermSet visited;
  std::vector<std::pair<Term, bool>> to_visit = { { term, false } };
  while (!to_visit.empty())
  {
    auto [t, children_done] = to_visit.back();
    to_visit.pop_back();
    bool pending = pending_definitions_.find(t) != pending_definitions_.end();
    if (children_done)
    {
      if (pending)
      {
        used.push_back(t);
      }
      continue;
    }
    if (!visited.insert(t).second)
    {
      continue;
    }
    // The model was found before these were declared, so it has nothing
    // to say about them; the binary does not even know them yet.
    std::string unknown;
    if (pending_symbols_.find(t) != pending_symbols_.end())
    {
      unknown = "the symbol " + t->to_string();
    }
    else if (uses_held_back_sort(t->get_sort()))
    {
      unknown = "the sort " + t->get_sort()->to_string();
    }
    if (!unknown.empty())
    {
      throw IncorrectUsageException(operation + " can't read "
                                    + term->to_string() + ": it uses " + unknown
                                    + ", declared since the last check");
    }
    std::shared_ptr<GenericTerm> gt = backend_pointer_cast<GenericTerm>(t);
    if (!pending && gt->is_ground())
    {
      continue;
    }
    to_visit.push_back({ t, true });
    for (const Term & c : gt->get_children())
    {
      to_visit.push_back({ c, false });
    }
  }

  // Bind them with nested lets, the first one outermost, since a let's
  // bindings cannot refer to one another.
  std::string text = name;
  for (auto it = used.rbegin(); it != used.rend(); ++it)
  {
    text = "(let ((" + term_name(*it) + " " + to_smtlib_def(*it) + ")) " + text
           + ")";
  }
  return text;
}

void GenericSolver::close_solver() const
{
  // closing our end of the solver's stdin first lets a well-behaved binary
  // see the end of its input and exit; the SIGKILL is the backstop, and is
  // what keeps waitpid() from blocking behind a solver deep in a search
  close_fd(outpipefd[1]);
  // kill() would read a pid of 0 or -1 as a whole group of processes
  if (pid > 0)
  {
    kill(pid, SIGKILL);
    waitpid(pid, &status, 0);
    pid = -1;
  }
  close_fd(inpipefd[0]);
}

void GenericSolver::define_fun(std::string name,
                               SortVec args_sorts,
                               Sort res_sort,
                               Term defining_term) const
{
  // The command below writes an empty parameter list, so arguments would be
  // dropped rather than declared: only define-const style definitions work.
  if (!args_sorts.empty())
  {
    throw NotImplementedException(
        "The generic solver can only define functions without parameters");
  }
  // send a define-fun to the binary
  if (send_or_hold(DEFINE_FUN_STR,
                   name,
                   "()",
                   sort_name(res_sort),
                   to_smtlib_def(defining_term)))
  {
    pending_definitions_.insert(defining_term);
  }
}

std::string GenericSolver::sort_name(const Sort & sort) const
{
  std::string name = sort->to_string();
  // the same name is not enough: another backend's sort can print alike
  auto it = name_sort_map.find(name);
  if (it == name_sort_map.end() || it->second != sort)
  {
    throw IncorrectUsageException("Sort " + name
                                  + " was not made by this solver");
  }
  return name;
}

std::string GenericSolver::term_name(const Term & term) const
{
  // operator[] would file an unknown term under an empty name
  auto it = term_name_map.find(term);
  if (it == term_name_map.end())
  {
    throw IncorrectUsageException("Term " + term->to_string()
                                  + " was not made by this solver");
  }
  return it->second;
}

std::string GenericSolver::to_smtlib_def(Term term) const
{
  std::shared_ptr<GenericTerm> gt = backend_pointer_cast<GenericTerm>(term);
  // a term without an op is its name
  if (gt->get_op().is_null())
  {
    return gt->to_string();
  }
  // the children by the names the binary knows them by
  return smtlib_application(gt->get_op(),
                            gt->get_children(),
                            [this](const Term & t) { return term_name(t); });
}

Sort GenericSolver::make_sort(const Sort & sort_con,
                              const SortVec & sorts) const
{
  // Nothing is sent to the binary: (declare-sort List 1) went out when the
  // constructor itself was made, and an application like (List Int) is a sort
  // term, not a declaration. Mismatched arity throws from the sort.
  Sort sort = std::make_shared<UninterpretedGenericSort>(sort_con, sorts);
  const std::string name = sort->to_string();
  // Applying the same constructor to the same sorts twice names the same
  // sort, so unlike declare-sort this is not a clash.
  auto known = name_sort_map.find(name);
  if (known != name_sort_map.end())
  {
    return known->second;
  }
  name_sort_map[name] = sort;
  return sort;
}

Sort GenericSolver::make_sort(const std::string name, std::uint64_t arity) const
{
  // when creating a new uninterpreted sort, the name
  // must be new.
  if (name_sort_map.find(name) == name_sort_map.end())
  {
    // create the sort
    Sort sort = std::make_shared<UninterpretedGenericSort>(name, arity);
    // store the sort and the name in the maps
    name_sort_map[name] = sort;
    // declare the sort to the binary of the solver
    if (send_or_hold(DECLARE_SORT_STR, name, std::to_string(arity)))
    {
      pending_sort_names_.insert(name);
    }
    return sort;
  }
  else
  {
    throw IncorrectUsageException("sort name: " + name + " already taken");
  }
}

Sort GenericSolver::make_sort(const SortKind sk) const
{
  if (sk != BOOL && sk != INT && sk != REAL)
  {
    throw IncorrectUsageException("Can't create sort from " + to_string(sk));
  }
  // create the sort
  Sort sort = std::make_shared<GenericSort>(sk);
  // compute the name of the sort
  std::string name = sort->to_string();

  // note that nothing needs to be communicated to the solver,
  // as in this case the sort is built in.

  // store in local maps if needed, and return the sort
  if (name_sort_map.find(name) == name_sort_map.end())
  {
    name_sort_map[name] = sort;
    return sort;
  }
  else
  {
    return name_sort_map.at(name);
  }
}

Sort GenericSolver::make_sort(const SortKind sk, std::uint64_t size) const
{
  if (sk != BV)
  {
    throw IncorrectUsageException("Can't create sort from " + to_string(sk)
                                  + " and " + std::to_string(size));
  }
  // create the sort
  Sort sort = std::make_shared<BVGenericSort>(size);
  // compute the name
  std::string name = sort->to_string();

  // note that nothing needs to be communicated to the solver,
  // as in this case the sort is built in.

  // store in maps if needed and return the sort
  if (name_sort_map.find(name) == name_sort_map.end())
  {
    name_sort_map[name] = sort;
    return sort;
  }
  else
  {
    return name_sort_map.at(name);
  }
}

Sort GenericSolver::make_sort(SortKind sk, const SortVec & sorts) const
{
  // create the sort
  Sort sort;
  if (sk == FUNCTION)
  {
    SortVec domain(sorts);
    Sort codomain = domain.back();
    domain.pop_back();
    sort = std::make_shared<FunctionGenericSort>(domain, codomain);
  }
  else if (sk == ARRAY && sorts.size() == 2)
  {
    sort = std::make_shared<ArrayGenericSort>(sorts[0], sorts[1]);
  }
  else
  {
    std::string msg("Can't make sort from ");
    msg += to_string(sk);
    for (auto ss : sorts)
    {
      msg += " " + ss->to_string();
    }
    throw IncorrectUsageException(msg);
  }
  // compute the name
  std::string name = sort->to_string();

  // note that nothing needs to be communicated to the solver,
  // as in this case the sort is built in, or can used
  // by combining sorts that were already defined.

  // store in maps if needed and return the sort
  if (name_sort_map.find(name) == name_sort_map.end())
  {
    name_sort_map[name] = sort;
    return sort;
  }
  else
  {
    return name_sort_map.at(name);
  }
}

SortVec GenericSolver::make_datatype_sorts(
    const std::vector<DatatypeDecl> & decls) const
{
  // Every declaration is checked before any is used, so that a refused
  // list declares none of its datatypes.
  std::vector<std::shared_ptr<GenericDatatype>> datatypes;
  std::vector<std::string> dt_names;
  std::unordered_set<std::string> seen_names;
  datatypes.reserve(decls.size());
  dt_names.reserve(decls.size());
  for (const DatatypeDecl & d : decls)
  {
    auto gdt_decl = backend_pointer_cast<GenericDatatypeDecl>(d);
    auto dt_it = decl_datatype_map.find(gdt_decl);
    if (dt_it == decl_datatype_map.end())
    {
      detail::throw_foreign_handle(d);
    }
    auto name = gdt_decl->get_name();
    if (name_sort_map.find(name) != name_sort_map.end()
        || !seen_names.insert(name).second)
    {
      throw IncorrectUsageException("sort name: " + name + " already taken");
    }
    datatypes.push_back(dt_it->second);
    dt_names.push_back(name);
  }

  SortVec dt_sorts;
  // SMT-LIB declares at least one datatype per command
  if (datatypes.empty())
  {
    return dt_sorts;
  }
  dt_sorts.reserve(datatypes.size());
  std::string names_text;
  std::string bodies_text;
  for (size_t i = 0; i < datatypes.size(); ++i)
  {
    auto curr_dt = datatypes[i];
    // The sort keeps copies of the constructors, so that a constructor
    // declaration changed or added to another datatype later does not
    // change it.
    for (DatatypeConstructorDecl & con : curr_dt->cons_decl_vector)
    {
      auto orig = std::static_pointer_cast<GenericDatatypeConstructorDecl>(con);
      auto copy =
          std::make_shared<GenericDatatypeConstructorDecl>(orig->cons_name);
      copy->selector_vector = orig->selector_vector;
      copy->dt_decl = orig->dt_decl;
      con = copy;
    }
    Sort dt_sort = std::make_shared<GenericDatatypeSort>(curr_dt);
    // Replaces the sort of any selectors with a false finalized field
    // with dt_sort and sets finalized to true.
    curr_dt->change_sort_of_selector(dt_sort);
    dt_sorts.push_back(dt_sort);

    names_text += (i == 0 ? "(" : " (") + dt_names[i] + " 0)";
    bodies_text += "(";
    for (const DatatypeConstructorDecl & con : curr_dt->get_cons_vector())
    {
      auto gcon = std::static_pointer_cast<GenericDatatypeConstructorDecl>(con);
      bodies_text += " (" + gcon->get_name();
      for (const auto & sel : gcon->get_selector_vector())
      {
        bodies_text += " ( " + sel.name + " " + sel.sort->to_string() + " )";
      }
      bodies_text += ")";
    }
    bodies_text += ")\n";
  }

  std::string to_solver = "(";
  to_solver += DECLARE_DATATYPE_STR;
  to_solver += " (" + names_text + ") (\n" + bodies_text + "))";
  for (size_t i = 0; i < dt_sorts.size(); ++i)
  {
    name_sort_map[dt_names[i]] = dt_sorts[i];
  }
  if (send_or_hold(to_solver))
  {
    pending_sort_names_.insert(dt_names.begin(), dt_names.end());
  }
  return dt_sorts;
}

Sort GenericSolver::make_sort(const DatatypeDecl & d) const
{
  return make_datatype_sorts({ d })[0];
}

DatatypeDecl GenericSolver::make_datatype_decl(const std::string & s) const
{
  auto new_dt_decl = std::make_shared<GenericDatatypeDecl>(s);
  auto new_dt = std::make_shared<GenericDatatype>(new_dt_decl);
  decl_datatype_map[new_dt_decl] = new_dt;
  datatype_name_map[new_dt] = s;
  return new_dt_decl;
}

/** throw if a name a user chose for a term or function lies where the
 * generic solver makes up names of its own
 * @param name the name chosen
 * @param what what is being named, for the message
 * @throws IncorrectUsageException if the name starts with
 * INTERNAL_NAME_PREFIX
 */
static void refuse_internal_name(const std::string & name,
                                 const std::string & what)
{
  if (is_internal_name(name))
  {
    throw IncorrectUsageException(
        what + " name " + name + " starts with "
        + std::string(INTERNAL_NAME_PREFIX)
        + ", which the generic solver keeps for names of its own");
  }
}

DatatypeConstructorDecl GenericSolver::make_datatype_constructor_decl(
    const std::string s) const
{
  refuse_internal_name(s, "constructor");
  std::shared_ptr<GenericDatatypeConstructorDecl> new_dt_cons_decl =
      std::shared_ptr<GenericDatatypeConstructorDecl>(
          new GenericDatatypeConstructorDecl(s));
  return new_dt_cons_decl;
}

void GenericSolver::add_constructor(DatatypeDecl & dt,
                                    const DatatypeConstructorDecl & con) const
{
  auto gdt_decl = backend_pointer_cast<GenericDatatypeDecl>(dt);
  auto dt_it = decl_datatype_map.find(gdt_decl);
  if (dt_it == decl_datatype_map.end())
  {
    detail::throw_foreign_handle(dt);
  }
  // a sort the datatype was used for holds this same datatype, and the
  // binary has its declaration already
  auto name = gdt_decl->get_name();
  if (name_sort_map.find(name) != name_sort_map.end())
  {
    throw IncorrectUsageException("Datatype " + name
                                  + " cannot change, since the sort name "
                                  + name + " is already taken");
  }
  dt_it->second->add_constructor(con);
}

void GenericSolver::add_selector(DatatypeConstructorDecl & dt,
                                 const std::string & name,
                                 const Sort & s) const
{
  refuse_internal_name(name, "selector");
  std::shared_ptr<SelectorComponents> newSelector =
      std::make_shared<SelectorComponents>();
  newSelector->name = name;
  newSelector->sort = s;
  newSelector->finalized = true;
  std::shared_ptr<GenericDatatypeConstructorDecl> gdtc =
      backend_pointer_cast<GenericDatatypeConstructorDecl>(dt);
  gdtc->add_new_selector(*newSelector);
}

void GenericSolver::add_selector_self(DatatypeConstructorDecl & dt,
                                      const std::string & name) const
{
  refuse_internal_name(name, "selector");
  std::shared_ptr<SelectorComponents> newSelector =
      std::make_shared<SelectorComponents>();
  std::shared_ptr<GenericDatatypeConstructorDecl> gdt_cons =
      backend_pointer_cast<GenericDatatypeConstructorDecl>(dt);

  newSelector->name = name;
  // The constructor may not belong to a datatype yet, so the sort is left
  // null; make_sort gives the datatype's sort to its copy of the selector.
  newSelector->finalized = false;
  gdt_cons->add_new_selector(*newSelector);
}

Term GenericSolver::get_constructor(const Sort & s, std::string name) const
{
  std::shared_ptr<GenericDatatype> dt =
      backend_pointer_cast<GenericSort>(s)->get_generic_datatype();
  bool found = false;
  for (int i = 0; i < dt->get_num_constructors(); ++i)
  {
    if (std::static_pointer_cast<GenericDatatypeConstructorDecl>(
            dt->get_cons_vector()[i])
            ->get_name()
        == name)
    {
      found = true;
      break;
    }
  }
  if (!found)
  {
    throw IncorrectUsageException("Constructor not in datatype");
  }
  Sort cons_sort =
      std::make_shared<DatatypeComponentSort>(CONSTRUCTOR, name, s);
  Term new_term =
      std::make_shared<GenericTerm>(cons_sort, Op(), TermVec{}, name);
  term_name_map[new_term] = name;
  return new_term;
}

Term GenericSolver::get_tester(const Sort & s, std::string name) const
{
  std::shared_ptr<GenericDatatype> dt =
      backend_pointer_cast<GenericSort>(s)->get_generic_datatype();
  bool found = false;
  for (int i = 0; i < dt->get_num_constructors(); ++i)
  {
    if (std::static_pointer_cast<GenericDatatypeConstructorDecl>(
            dt->get_cons_vector()[i])
            ->get_name()
        == name)
    {
      found = true;
      break;
    }
  }
  if (!found)
  {
    throw IncorrectUsageException("Constructor not in datatype");
  }

  Sort cons_sort = std::make_shared<DatatypeComponentSort>(TESTER, name, s);
  // SMT-LIB writes a tester as an indexed identifier
  std::string tester = "(_ is " + smtlib_quote_symbol(name) + ")";
  Term new_term =
      std::make_shared<GenericTerm>(cons_sort, Op(), TermVec{}, tester);
  term_name_map[new_term] = tester;
  return new_term;
}

Term GenericSolver::get_selector(const Sort & s,
                                 std::string con,
                                 std::string name) const
{
  std::shared_ptr<GenericDatatype> dt =
      backend_pointer_cast<GenericSort>(s)->get_generic_datatype();
  bool found = false;
  Sort cons_sort = std::make_shared<DatatypeComponentSort>(SELECTOR, name, s);
  for (int i = 0; i < dt->get_num_constructors(); ++i)
  {
    std::shared_ptr<GenericDatatypeConstructorDecl> curr_con =
        std::static_pointer_cast<GenericDatatypeConstructorDecl>(
            dt->get_cons_vector()[i]);
    if (curr_con->get_name() == con)
    {
      for (int f = 0; f < curr_con->get_selector_count(); ++f)
      {
        if (((curr_con->get_selector_vector())[f]).name == name)
        {
          found = true;
          std::static_pointer_cast<DatatypeComponentSort>(cons_sort)
              ->set_selector_sort(((curr_con->get_selector_vector())[f]).sort);
          break;
        }
      }
    }
  }
  if (!found)
  {
    throw IncorrectUsageException("Selector not in datatype");
  }
  Term new_term =
      std::make_shared<GenericTerm>(cons_sort, Op(), TermVec{}, name);
  term_name_map[new_term] = name;
  return new_term;
}

Term GenericSolver::store_term(Term term) const
{
  // cast the term to a GenericTerm
  std::shared_ptr<GenericTerm> gterm = backend_pointer_cast<GenericTerm>(term);
  // store the term in the maps in case it is not there already
  if (term_name_map.find(gterm) == term_name_map.end())
  {
    std::string name;
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
    //
    // A value needs no define-fun either, since its own SMT-LIB text names
    // it. That matters beyond brevity: a definition would move the binary
    // out of a query mode, taking with it the model a caller reading one
    // out is in the middle of. For the same reason, a term made in the sat
    // or unsat mode is defined only by the next command that leaves it,
    // and a query before then binds it with a let (see query_text).
    if (gterm->is_value())
    {
      name = to_smtlib_def(gterm);
    }
    else if (gterm->is_ground())
    {
      // an internal name with a running index. The binary keeps these for
      // good, so they are names no user can take: make_symbol and
      // make_param refuse them.
      term_counter++;
      name = internal_name("term", term_counter);
      define_fun(name, SortVec{}, gterm->get_sort(), gterm);
      // The binary can name the definition back, in an unsat core.
      name_term_map[name] = gterm;
    }
    else
    {
      name = to_smtlib_def(gterm);
    }
    term_name_map[gterm] = name;
  }
  // The term stored first, which an equal term made later stands for
  return term_name_map.find(gterm)->first;
}

Term GenericSolver::make_non_negative_bv_const(std::string abs_decimal,
                                               std::uint64_t width) const
{
  Sort bvsort = make_sort(BV, width);
  std::string repr = "#b" + bv_value_to_bits(abs_decimal, 10, bvsort);
  Term term = std::make_shared<GenericTerm>(bvsort, Op(), TermVec{}, repr);
  return store_term(term);
}

Term GenericSolver::make_non_negative_bv_const(std::int64_t i,
                                               std::uint64_t width) const
{
  return make_non_negative_bv_const(std::to_string(i), width);
}

Term GenericSolver::make_negative_bv_const(std::string abs_decimal,
                                           std::uint64_t width) const
{
  return make_non_negative_bv_const("-" + abs_decimal, width);
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

/** Throws unless a value of sort kind sk can be made from a number */
static void check_value_sort_kind(SortKind sk)
{
  if (sk != BV && sk != INT && sk != REAL)
  {
    throw IncorrectUsageException("Can't make a value of sort kind "
                                  + to_string(sk) + " from a number");
  }
}

Term GenericSolver::make_term(std::int64_t i, const Sort & sort) const
{
  Term value_term = make_value(i, sort);
  return store_term(value_term);
}

Term GenericSolver::make_value(std::int64_t i, const Sort & sort) const
{
  SortKind sk = sort->get_sort_kind();
  check_value_sort_kind(sk);
  if (sk == INT || sk == REAL)
  {
    std::string repr = smtlib_arith_value(sk, std::to_string(i));
    Term term = std::make_shared<GenericTerm>(sort, Op(), TermVec{}, repr);
    return term;
  }
  else
  {
    // sk == BV
    std::string repr = "#b" + bv_value_to_bits(std::to_string(i), 10, sort);
    Term term = std::make_shared<GenericTerm>(sort, Op(), TermVec{}, repr);
    return term;
  }
}

Term GenericSolver::make_term(const std::string val,
                              const Sort & sort,
                              std::uint64_t base) const
{
  Term value_term = make_value(val, sort, base);
  return store_term(value_term);
}

Term GenericSolver::make_value(const std::string val,
                               const Sort & sort,
                               std::uint64_t base) const
{
  SortKind sk = sort->get_sort_kind();
  check_value_sort_kind(sk);
  std::string repr;
  if (sk == INT || sk == REAL)
  {
    std::string decimal = arith_value_to_decimal(sk, val, base);
    // a solver binary reads some other strings, such as the name of a
    // symbol or a decimal for an INT, without an error but not as the
    // number meant
    if (!is_arith_number(sk, decimal))
    {
      throw IncorrectUsageException("Value " + val + " is not a number of sort "
                                    + sort->to_string());
    }
    // no binary reads a number with spaces in it
    std::string number = decimal;
    number.erase(std::remove(number.begin(), number.end(), ' '), number.end());
    // a division by zero is a legal term, but not a number
    std::string::size_type slash = number.find('/');
    if (slash != std::string::npos
        && number.find_first_not_of('0', slash + 1) == std::string::npos)
    {
      throw IncorrectUsageException("Value " + val + " divides by zero");
    }
    repr = smtlib_arith_value(sk, number);
    Term term = std::make_shared<GenericTerm>(sort, Op(), TermVec{}, repr);
    return term;
  }
  else
  {
    // sk == BV
    repr = "#b" + bv_value_to_bits(val, base, sort);
    Term term = std::make_shared<GenericTerm>(sort, Op(), TermVec{}, repr);
    return term;
  }
}

Term GenericSolver::make_term(const Term & val, const Sort & sort) const
{
  if (sort->get_sort_kind() != ARRAY)
  {
    throw IncorrectUsageException("Can't make a constant array of sort "
                                  + sort->to_string()
                                  + ", which is not an array sort");
  }
  if (sort->get_elemsort() != val->get_sort())
  {
    throw IncorrectUsageException(
        "Can't make a constant array of sort " + sort->to_string() + " from "
        + val->to_string() + " of sort " + val->get_sort()->to_string());
  }
  std::string repr = smtlib_const_array(sort_name(sort), term_name(val));
  Term term = std::make_shared<GenericTerm>(sort, Op(), TermVec{ val }, repr);
  return store_term(term);
}

Term GenericSolver::make_symbol(const std::string name, const Sort & sort)
{
  refuse_internal_name(name, "symbol");
  // Bars only where SMT-LIB needs them, as they do not change the symbol
  std::string quoted_name = smtlib_quote_symbol(name);
  if (name_term_map.find(quoted_name) != name_term_map.end())
  {
    throw IncorrectUsageException("symbol name: " + name + " already taken");
  }

  // looked up first, so an unknown sort leaves no symbol behind
  std::string sort_str = sort_name(sort);

  // create the sumbol and store it in the maps
  Term term =
      std::make_shared<GenericTerm>(sort, Op(), TermVec{}, quoted_name, true);
  name_term_map[quoted_name] = term;
  term_name_map[term] = quoted_name;

  // communicate the creation of the symbol to the binary of the solver.
  // When the sort is not a function, we specify an empty domain.
  // Otherwise, the name of the sort includes the domain.
  if (sort->get_sort_kind() == FUNCTION
          ? send_or_hold(DECLARE_FUN_STR, quoted_name, sort_str)
          : send_or_hold(DECLARE_FUN_STR, quoted_name, "()", sort_str))
  {
    pending_symbols_.insert(term);
  }

  return term;
}

Term GenericSolver::get_symbol(const std::string & name) const
{
  // The map holds the binary's own names too, which no symbol can have.
  auto it = is_internal_name(name)
                ? name_term_map.end()
                : name_term_map.find(smtlib_quote_symbol(name));
  if (it == name_term_map.end())
  {
    throw IncorrectUsageException("Symbol named " + name + " does not exist.");
  }
  return it->second;
}

Term GenericSolver::make_param(const std::string name, const Sort & sort) const
{
  refuse_internal_name(name, "param");
  if (!param_names_.insert(name).second)
  {
    throw IncorrectUsageException("param name: " + name
                                  + " already taken by another param");
  }
  // The param prints as the user named it, and is told apart from a symbol
  // of that name by being a param. SMT-LIB reads a symbol |x| as x, so a
  // binder of x would capture it: the binary sees the param under a name
  // no symbol can have.
  Term term = std::make_shared<GenericTerm>(
      sort, Op(), TermVec{}, smtlib_quote_symbol(name), false);
  term_counter++;
  term_name_map[term] = internal_name("param", term_counter);
  return term;
}

/**
 * base raised to exponent, as products found by repeated squaring, so the
 * term grows with the number of digits of the exponent rather than with it
 */
static Term make_power(const GenericSolver & solver,
                       const Term & base,
                       std::int64_t exponent)
{
  if (exponent == 0)
  {
    return solver.make_term(1, base->get_sort());
  }
  if (exponent == 1)
  {
    return base;
  }
  Term half = make_power(solver, base, exponent / 2);
  Term square = solver.make_term(Mult, half, half);
  return exponent % 2 == 0 ? square : solver.make_term(Mult, square, base);
}

Term GenericSolver::make_term(const Op op, const TermVec & terms) const
{
  if (op.prim_op == Forall || op.prim_op == Exists)
  {
    check_quantifier_binders(op, terms);
  }
  else if (op.prim_op == Divisible && op.indices[0] < 1)
  {
    throw IncorrectUsageException("Can't create divisible with index < 1");
  }

  // A power to a constant exponent is unfolded, as not all solvers support it.
  if (op.prim_op == Pow && terms.size() == 2 && terms[1]->is_value())
  {
    if (!check_sortedness(op, terms))
    {
      throw IncorrectUsageException(
          "Pow takes an Int base and an Int exponent");
    }
    const std::int64_t exponent = terms[1]->to_signed_int();
    if (exponent >= 0)
    {
      return make_power(*this, terms[0], exponent);
    }
    Sort sort = terms[0]->get_sort();
    Term one = make_term(1, sort);
    Term minus_one = make_term(-1, sort);
    // We can always compute exponents of 1 and -1.
    return make_term(Ite,
                     make_term(Equal, terms[0], one),
                     one,
                     make_term(Ite,
                               make_term(Equal, terms[0], minus_one),
                               exponent % 2 == 0 ? one : minus_one,
                               make_term(0, sort)));
  }

  // a quantifier binds one parameter (see ops.cpp), so `forall x y . body`
  // is made as `forall x . forall y . body`
  if ((op.prim_op == Forall || op.prim_op == Exists) && terms.size() > 2)
  {
    Term body = terms.back();
    for (auto it = std::next(terms.rbegin()); it != terms.rend(); ++it)
    {
      body = make_term(op, TermVec{ *it, body });
    }
    return body;
  }
  Sort sort = compute_sort(op, this, terms);
  std::string repr = "(" + op.to_string();
  for (size_t i = 0; i < terms.size(); i++)
  {
    repr += " " + term_name(terms[i]);
  }
  repr += ")";
  Term term = std::make_shared<GenericTerm>(sort, op, terms, repr);
  try
  {
    return store_term(term);
  }
  catch (IncorrectUsageException &)
  {
    // The sorts are checked, so a binary refusing a power, which has a
    // symbolic exponent here, does not read SMT-LIB's **.
    if (op.prim_op != Pow)
    {
      throw;
    }
    throw NotImplementedException(
        "The binary does not read SMT-LIB's **, which a power to a symbolic "
        "exponent needs");
  }
}

Term GenericSolver::get_value(const Term & t) const
{
  // only values of these sorts can be read back
  Sort sort = t->get_sort();
  SortKind sk = sort->get_sort_kind();
  if (sk != BOOL && sk != BV && sk != INT && sk != REAL)
  {
    throw NotImplementedException(
        "The generic solver cannot get the value of a term of sort kind "
        + to_string(sk));
  }

  // get the name of the term (the way the term is defined in the solver)
  auto name_it = term_name_map.find(t);
  if (name_it == term_name_map.end())
  {
    throw IncorrectUsageException("Can't get the value of " + t->to_string()
                                  + ": it was not made by this solver");
  }
  require_mode(SmtLibMode::SAT,
               "get_value",
               "the last check must have answered sat or unknown");

  // ask the binary for the value and parse it
  std::string result =
      run_command(CommandKind::GET,
                  GET_VALUE_STR,
                  "(" + query_text(name_it->first, "get_value") + ")");

  std::string value = strip_value_from_result(result);

  return value_from_string(value, sort);
}

Term GenericSolver::value_from_string(const std::string & value,
                                      const Sort & sort) const
{
  const SortKind sk = sort->get_sort_kind();
  Term resulting_term;
  // for bit-vectors, we distinguish between the solver's way of representing
  // them. it can be either binary, hex, or decimal.
  if (sk == BV)
  {
    if (value.substr(0, 2) == "#b")
    {
      // binary representation
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
      const std::string prefix = "(_ bv";
      std::size_t end_of_decimal =
          value.find_first_not_of("0123456789", prefix.size());
      if (value.compare(0, prefix.size(), prefix) != 0
          || end_of_decimal == prefix.size()
          || end_of_decimal == std::string::npos)
      {
        throw InternalSolverException("Unexpected bit-vector value: " + value);
      }
      std::string decimal =
          value.substr(prefix.size(), end_of_decimal - prefix.size());
      resulting_term = make_value(decimal, sort, 10);
    }
  }
  else if (sk == BOOL)
  {
    if (value != "true" && value != "false")
    {
      throw InternalSolverException("Unexpected Boolean value: " + value);
    }
    bool b = (value == "true");
    resulting_term = make_value(b);
  }
  else if (sk == INT || sk == REAL)
  {
    // the binary's answer, such as (- 5), is already SMT-LIB, unlike the
    // number strings make_value takes
    resulting_term =
        std::make_shared<GenericTerm>(sort, Op(), TermVec{}, value);
  }
  else
  {
    throw NotImplementedException(
        "The generic solver cannot read back a value of sort kind "
        + to_string(sk));
  }
  return resulting_term;
}

std::string GenericSolver::strip_value_from_result(std::string result) const
{
  // the response is ((<name> <value>)), where <name> is a symbol, possibly
  // |quoted|, and <value> is any term, such as (- 5) or (_ bv5 4). Solvers
  // differ in the spacing between the parentheses.
  const std::string unexpected = "Unexpected get-value response: " + result;
  std::string inner = trim(result);
  for (int depth = 0; depth < 2; depth++)
  {
    if (inner.size() < 2 || inner.front() != '(' || inner.back() != ')')
    {
      throw InternalSolverException(unexpected);
    }
    inner = inner.substr(1, inner.size() - 2);
    trim(inner);
  }

  // the term asked about, which get-value echoes back, is one
  // s-expression: a symbol, quoted or not, or a term printed in full
  if (inner.empty())
  {
    throw InternalSolverException(unexpected);
  }
  std::string::size_type end_of_name = sexpr_end(inner, 0);
  if (end_of_name == std::string::npos)
  {
    throw InternalSolverException(unexpected);
  }

  std::string value = inner.substr(end_of_name);
  trim(value);
  if (value.empty())
  {
    throw InternalSolverException(unexpected);
  }
  return value;
}

void GenericSolver::get_unsat_assumptions(UnorderedTermSet & out) const
{
  require_mode(SmtLibMode::UNSAT,
               "get_unsat_assumptions",
               "the last check must have answered unsat");
  std::string result = run_command(CommandKind::GET, GET_UNSAT_ASSUMPTIONS_STR);

  // parse the result -- get the assumptions
  UnorderedTermSet assumptions = get_assumptions_from_string(result);

  // put the result in out, each label as the formula it stands for
  for (const Term & a : assumptions)
  {
    auto it = labelled_assumptions.find(a);
    out.insert(it == labelled_assumptions.end() ? a : it->second);
  }
}

UnorderedTermSet GenericSolver::get_assumptions_from_string(
    std::string result) const
{
  // the result from the solver is a list of Boolean literals, each a
  // symbol or its negation
  const auto literal_list = split_sexpr(trim(result));
  if (!literal_list)
  {
    throw InternalSolverException("Unexpected get-unsat-assumptions response: "
                                  + result);
  }

  UnorderedTermSet literals;
  for (const std::string & literal : *literal_list)
  {
    std::string name = literal;
    bool positive = true;
    if (const auto parts = split_sexpr(literal))
    {
      if (parts->size() != 2 || (*parts)[0] != "not")
      {
        throw InternalSolverException(
            "Unexpected get-unsat-assumptions response: " + result);
      }
      name = (*parts)[1];
      positive = false;
    }

    // A binary may write a name in bars or without, which SMT-LIB reads as
    // the same symbol, so the name is looked up as this solver writes it.
    name = smtlib_unquote_symbol(name);
    auto it = name_term_map.find(smtlib_quote_symbol(name));
    if (it == name_term_map.end())
    {
      throw InternalSolverException(
          "The get-unsat-assumptions response names an unknown term " + name
          + ": " + result);
    }
    literals.insert(positive ? it->second : make_term(Not, it->second));
  }
  return literals;
}

UnorderedTermMap GenericSolver::get_array_values(const Term & arr,
                                                 Term & out_const_base) const
{
  out_const_base = nullptr;

  const Sort sort = arr->get_sort();
  if (sort->get_sort_kind() != ARRAY)
  {
    throw IncorrectUsageException("Can't get the array values of "
                                  + arr->to_string()
                                  + ", which is not an array");
  }

  auto name_it = term_name_map.find(arr);
  if (name_it == term_name_map.end())
  {
    throw IncorrectUsageException("Can't get the value of " + arr->to_string()
                                  + ": it was not made by this solver");
  }

  require_mode(SmtLibMode::SAT,
               "get_array_values",
               "the last check must have answered sat or unknown");

  std::string result =
      run_command(CommandKind::GET,
                  GET_VALUE_STR,
                  "(" + query_text(name_it->first, "get_array_values") + ")");
  std::string value = strip_value_from_result(result);

  // A binary writes an array value as a chain of stores over a base,
  // outermost store first.
  const Sort indexsort = sort->get_indexsort();
  const Sort elemsort = sort->get_elemsort();
  std::vector<std::pair<Term, Term>> stores;
  auto parts = split_sexpr(value);
  while (parts && parts->size() == 4 && (*parts)[0] == "store")
  {
    // store each term, so that a caller can read the array at an index this
    // returns: a term the binary has no name for cannot be printed to it
    stores.push_back({ store_term(value_from_string((*parts)[2], indexsort)),
                       store_term(value_from_string((*parts)[3], elemsort)) });
    value = (*parts)[1];
    parts = split_sexpr(value);
  }

  // Under the stores stands ((as const <sort>) <base>) where the binary
  // gives a constant base.
  const auto head =
      parts && parts->size() == 2 ? split_sexpr((*parts)[0]) : std::nullopt;
  if (!head || head->size() != 3 || (*head)[0] != "as" || (*head)[1] != "const")
  {
    // Say which head turned up rather than return a map that quietly omits
    // whatever it holds.
    throw NotImplementedException(
        "The generic solver's binary gave an array "
        "model headed by "
        + value + ", which has no constant base");
  }
  out_const_base = store_term(value_from_string((*parts)[1], elemsort));

  return store_chain_values(stores);
}

void GenericSolver::do_reset()
{
  run_command(CommandKind::RESET, RESET_STR);
  // the binary has forgotten the labels' declarations
  assumption_labels.clear();
  labelled_assumptions.clear();
  // and has nothing left that the held-back commands could build on
  pending_commands_.clear();
  pending_definitions_.clear();
  pending_symbols_.clear();
  pending_sort_names_.clear();
}

void GenericSolver::set_opt(const std::string option, const std::string value)
{
  // options of a binary's own are left to the binary
  for (std::string_view start_only : start_only_options)
  {
    if (option == start_only)
    {
      require_mode(SmtLibMode::START,
                   "set_opt(\"" + option + "\")",
                   "only options may precede it");
    }
  }
  // Some binaries also take 1 and 0 for these, which SMT-LIB does not.
  if (option == "produce-models" || option == "produce-unsat-assumptions"
      || option == "incremental")
  {
    run_command(CommandKind::OPTION,
                SET_OPTION_STR,
                ":" + option,
                bool_option_value(option, value) ? "true" : "false");
    return;
  }
  run_command(CommandKind::OPTION, SET_OPTION_STR, ":" + option, value);
}

void GenericSolver::set_logic(const std::string logic)
{
  // Binaries differ on whether a set-logic may follow a declaration, an
  // assertion or another set-logic, so that is left to the binary. The
  // commands held back come first, in the order they were made.
  // An empty name, or a prefix such as QF_ with no theory after it, is
  // never a logic, though the cvc5 executable reads it as propositional
  // logic.
  if (logic.empty() || logic.back() == '_')
  {
    throw IncorrectUsageException(logic + " is not a logic");
  }
  try
  {
    run_command(CommandKind::LOGIC, SET_LOGIC_STR, logic);
    return;
  }
  catch (NotImplementedException &)
  {
    // A binary may know names of its own beyond SMT-LIB's, so only an
    // SMT-LIB name it does not support is one it lacks.
    if (!is_smtlib_logic(logic))
    {
      throw IncorrectUsageException(logic + " is not a logic");
    }
    if (logic != "QF_EIA")
    {
      throw;
    }
  }
  catch (IncorrectUsageException &)
  {
    if (logic != "QF_EIA")
    {
      throw;
    }
  }
  // A binary without QF_EIA still solves the ** Pow is under QF_NIA, as far
  // as it can.
  set_logic("QF_NIA");
}

void GenericSolver::do_assert(const Term & t)
{
  // cast to generic term, as we need to print it to the solver
  std::shared_ptr<GenericTerm> lt = backend_pointer_cast<GenericTerm>(t);

  // obtain the name of the term from the internal map
  std::string name = term_name(lt);

  // communicate the assertion to the binary of the solver
  run_command(CommandKind::ASSERTION, ASSERT_STR, name);
}

Result GenericSolver::str_to_result(std::string result) const
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
  return str_to_result(run_command(CommandKind::CHECK, CHECK_SAT_STR));
}

Result GenericSolver::do_check_sat_assuming(const TermVec & assumptions)
{
  std::string names;
  for (Term t : assumptions)
  {
    if (t->get_sort()->get_sort_kind() != BOOL)
    {
      throw IncorrectUsageException("Expecting Boolean assumptions but got: "
                                    + t->to_string());
    }
    names += " " + assumption_name(t);
  }

  // send command to the solver and parse it
  return str_to_result(run_command(
      CommandKind::CHECK, CHECK_SAT_ASSUMING_STR, "(" + names + ")"));
}

std::string GenericSolver::assumption_name(const Term & assumption)
{
  auto name_it = term_name_map.find(assumption);
  if (name_it == term_name_map.end())
  {
    throw IncorrectUsageException("Can't assume " + assumption->to_string()
                                  + ": it was not made by this solver");
  }
  std::string name = name_it->second;
  bool is_literal = assumption->is_symbolic_const()
                    || (assumption->get_op() == Not
                        && (*assumption->begin())->is_symbolic_const());
  if (is_literal)
  {
    return name;
  }

  // SMT-LIB takes only literals as assumptions, and some binaries report a
  // defined name back as its definition, rewritten. So any other formula is
  // assumed through a label of its own, which the binary reports by name.
  auto it = assumption_labels.find(assumption);
  if (it == assumption_labels.end())
  {
    std::string label_name =
        internal_name("assump", assumption_labels.size() + 1);
    Term label = std::make_shared<GenericTerm>(
        assumption->get_sort(), Op(), TermVec{}, label_name, true);
    name_term_map[label_name] = label;
    term_name_map[label] = label_name;
    // global-declarations keeps the label once its scope is popped
    run_command(CommandKind::ASSERTION,
                DECLARE_FUN_STR,
                label_name,
                "()",
                sort_name(assumption->get_sort()));
    it = assumption_labels.emplace(assumption, label).first;
    labelled_assumptions[label] = assumption;
  }
  std::string label_name = term_name(it->second);
  // a pop takes the implication with it, so it goes in again every time
  run_command(CommandKind::ASSERTION,
              ASSERT_STR,
              "(=> " + label_name + " " + name + ")");
  return label_name;
}

void GenericSolver::do_push(std::uint64_t num)
{
  run_command(CommandKind::ASSERTION, PUSH_STR, std::to_string(num));
}

void GenericSolver::do_pop(std::uint64_t num)
{
  run_command(CommandKind::ASSERTION, POP_STR, std::to_string(num));
}

void GenericSolver::dump_smt2(std::string filename) const
{
  // The binary is in the state these commands bring a new one to. Of them,
  // what it still holds: nothing from before a reset, and no assertion of a
  // popped scope or from before a reset-assertions, while declarations and
  // definitions stay, under global-declarations.
  std::vector<std::pair<std::string, const std::string *>> kept;
  // where each pushed scope starts in kept
  std::vector<std::size_t> scope_starts;
  for (const std::string & cmd : accepted_commands_)
  {
    std::string name = cmd.substr(1, cmd.find_first_of(" )") - 1);
    if (name == RESET_STR)
    {
      kept.clear();
      scope_starts.clear();
    }
    else if (name == PUSH_STR)
    {
      std::size_t num = std::stoull(cmd.substr(name.size() + 2));
      scope_starts.insert(scope_starts.end(), num, kept.size());
    }
    else if (name == POP_STR || name == RESET_ASSERTIONS_STR)
    {
      std::size_t from = 0;
      if (name == POP_STR)
      {
        std::size_t num = std::stoull(cmd.substr(name.size() + 2));
        from = scope_starts[scope_starts.size() - num];
        scope_starts.resize(scope_starts.size() - num);
      }
      else
      {
        scope_starts.clear();
      }
      std::size_t end = from;
      for (std::size_t i = from; i < kept.size(); ++i)
      {
        if (kept[i].first != ASSERT_STR)
        {
          kept[end++] = kept[i];
        }
      }
      kept.resize(end);
    }
    else
    {
      kept.emplace_back(name, &cmd);
    }
  }

  std::ofstream out(filename);
  // SMT-LIB declares nothing before set-logic, so where the binary was left
  // to its default logic the dump sets ALL
  bool logic_set = false;
  for (const auto & [name, cmd] : kept)
  {
    if (name == SET_LOGIC_STR)
    {
      logic_set = true;
    }
    else if (!logic_set && name != SET_OPTION_STR)
    {
      out << "(" << SET_LOGIC_STR << " ALL)\n";
      logic_set = true;
    }
    out << *cmd << "\n";
  }
  if (!logic_set)
  {
    out << "(" << SET_LOGIC_STR << " ALL)\n";
  }
  out << "(" << CHECK_SAT_STR << ")\n";
}

void GenericSolver::do_reset_assertions()
{
  // global-declarations keeps declarations and definitions through it, so
  // the ones held back go in first
  run_command(CommandKind::RESET_ASSERTIONS, RESET_ASSERTIONS_STR);
}

}  // namespace smt
