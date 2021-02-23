#pragma once

#include <string>
#include <unordered_map>

#include "smt-switch/smt.h"
#include "smtlibparser.h"

#define YY_DECL yy::parser::symbol_type yylex(smt::SmtLibDriver & drv)
YY_DECL;

namespace smt
{

class SmtLibDriver
{
 public:
  SmtLibDriver(smt::SmtSolver & solver);

  int parse(const std::string & f);
  // The name of the file being parsed.
  std::string file;

  void scan_begin();
  void scan_end();

  /* getters and setters  */
  yy::location & location() { return location_; }

  smt::SmtSolver & solver() { return solver_; }

  /** Looks up a symbol by name
   *  Returns a null term if there is no known symbol
   *  with that name
   *  @return term
   */
  smt::Term lookup_symbol(const std::string & sym);

  /** Creates a new symbol
   *  This is a light wrapper around solver_->make_symbol
   *  s.t. you can look up the symbol by name later
   *  see lookup_symbol
   *  @param name the name of the symbol
   *  @param sort the sort of the symbol
   */
  void new_symbol(const std::string & name, const smt::Sort & sort);

  /** Look up a primitive operator by a string
   *  @param str the string representation of this PrimOp
   *  @return the associated PrimOp
   *  throws an exception if there's no match
   */
  PrimOp lookup_primop(const std::string & str);

 protected:
  yy::location location_;

  smt::SmtSolver solver_;

  std::unordered_map<std::string, smt::Term> symbols_;
};

} // namespace smt
