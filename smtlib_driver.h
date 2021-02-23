#pragma once

#include <string>
#include <unordered_map>

#include "smt-switch/smt.h"
#include "smtlibparser.h"

#define YY_DECL yy::parser::symbol_type yylex(smt::SmtLibDriver & drv)
YY_DECL;

namespace smt
{

/** Used to keep track of which command is currently being parsed */
enum Command
{
  SETLOGIC = 0,
  SETOPT,
  DECLARECONST,
  DECLAREFUN,
  DEFINEFUN,
  ASSERT,
  CHECKSAT,
  CHECKSATASSUMING,
  PUSH,
  POP,
  NONE /** this must stay at the end --
           can also be used for the number of Command enums */
};

// TODO: remove if never used
Command str_to_command(std::string cmd);

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

  void set_command(Command cmd);

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

  /** Create a define-fun macro
   *  @param name the name of the define-fun
   *  @param the definition
   *  @param the arguments to the define-fun
   *  stored in defs_ and def_args_
   */
  void define_fun(const std::string & name,
                  const smt::Term & def,
                  const smt::TermVec & args = {});

  /** Helper function for define-fun
   *  Renames the argument variables to avoid polluting global
   *  symbols
   *  Stores these in a separate data structure from symbols
   *  @param
   */
  // void declare_sorted_var()

 protected:
  yy::location location_;

  smt::SmtSolver solver_;

  Command
      current_command_;  ///< which smt-lib command is currently being processed

  std::unordered_map<std::string, smt::Term> symbols_;

  std::unordered_map<std::string, smt::Term>
      defs_;  ///< keeps track of define-funs
  std::unordered_map<std::string, smt::TermVec>
      def_args_;  ///< keeps track of define-fun
                  ///< arguments

  // useful constants
  std::string def_arg_prefix_;  ///< the prefix for renamed define-fun arguments
};

} // namespace smt
