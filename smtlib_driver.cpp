#include "smtlib_driver.h"

#include "assert.h"
#include "smtlibparser.h"
#include "smtlibparser_maps.h"

using namespace std;

namespace smt
{

SmtLibDriver::SmtLibDriver(smt::SmtSolver & solver)
  : solver_(solver)
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

} // namespace smt
