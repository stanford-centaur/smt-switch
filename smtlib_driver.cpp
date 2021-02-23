#include "smtlib_driver.h"

#include "assert.h"
#include "smtlibparser.h"
#include "smtlibparser_maps.h"

using namespace std;

namespace smt
{

// TODO remove this if never used
Command str_to_command(std::string cmd)
{
  if (cmd == "set-logic")
  {
    return SETLOGIC;
  }
  else if (cmd == "set-option")
  {
    return SETOPT;
  }
  else if (cmd == "declare-const")
  {
    return DECLARECONST;
  }
  else if (cmd == "define-fun")
  {
    return DEFINEFUN;
  }
  else if (cmd == "assert")
  {
    return ASSERT;
  }
  else if (cmd == "check-sat")
  {
    return CHECKSAT;
  }
  else if (cmd == "check-sat-assuming")
  {
    return CHECKSATASSUMING;
  }
  else if (cmd == "push")
  {
    return PUSH;
  }
  else if (cmd == "pop")
  {
    return POP;
  }
  else
  {
    throw SmtException("SmtLibDriver Unknown smt-lib command: " + cmd);
  }
}

SmtLibDriver::SmtLibDriver(smt::SmtSolver & solver)
    : solver_(solver),
      current_command_(Command::NONE),
      def_arg_prefix_("__defvar_")
{
  // dedicated true/false symbols
  // done this way because true/false can be used in other places
  // for example, when setting options
  symbols_["true"] = solver_->make_term(true);
  symbols_["false"] = solver_->make_term(false);
}

int SmtLibDriver::parse(const std::string & f)
{
  file = f;
  location_.initialize(&file);
  scan_begin();
  yy::parser parse(*this);
  // commented from calc++ example
  //parse.set_debug_level (trace_parsing);
  int res = parse();
  scan_end();
  return res;
}

void SmtLibDriver::set_command(Command cmd) { current_command_ = cmd; }

Term SmtLibDriver::lookup_symbol(const string & sym)
{
  Term symbol_term;
  assert(!symbol_term);
  auto it = symbols_.find(sym);
  if (it != symbols_.end())
  {
    symbol_term = it->second;
    assert(symbol_term);
  }
  return symbol_term;
}

void SmtLibDriver::new_symbol(const std::string & name, const smt::Sort & sort)
{
  Term fresh_symbol = solver_->make_symbol(name, sort);
  symbols_[name] = fresh_symbol;
}

PrimOp SmtLibDriver::lookup_primop(const std::string & str)
{
  return str2primop.at(str);
}

void SmtLibDriver::define_fun(const string & name,
                              const Term & def,
                              const TermVec & args)
{
  defs_[name] = def;
  def_args_[name] = args;
}

} // namespace smt
