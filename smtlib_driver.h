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

  /* Override-able functions corresponding to SMT-LIB commands */
  virtual void assert_formula(const smt::Term & assertion);

  virtual Result check_sat();

  virtual Result check_sat_assuming(const smt::TermVec & assumptions);

  virtual void push(uint64_t num = 1);

  virtual void pop(uint64_t num = 1);

  /* getters and setters  */
  yy::location & location() { return location_; }

  smt::SmtSolver & solver() { return solver_; }

  void set_command(Command cmd);

  Command current_command() { return current_command_; }

  /* Methods for use in flex/bison generated code */

  // TODO: not sure if we ever use the null term feature
  //       maybe should just throw an exception?
  /** Look up a symbol by name
   *  Returns a null term if there is no known symbol
   *  with that name
   *  @return term
   */
  smt::Term lookup_symbol(const std::string & sym);

  /** Look up the temporary symbol for a define-fun argument
   *  @param the name of the argument
   */
  smt::Term lookup_arg(const std::string & name);

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

  /** Apply a define fun
   *  @param defname the name of the define-fun
   *  @param args the arguments to apply it to
   *         the parameter args from the define-fun
   *         declaration will be replaced by these arguments
   */
  Term apply_define_fun(const std::string & defname, const smt::TermVec & args);

  /** Helper function for define-fun - similar to new_symbol
   *  Associates an argument with a temporary symbol for
   *  define-fun arguments
   *  Renames the arguments to avoid polluting global symbols
   *  Stores these in a separate data structure from symbols
   *  @param name the name of the argument
   *  @param sort the sort of the argument
   *  @return the renamed term
   *  Note: creates new renamed variables as needed
   *  These aren't used except in the definition and will always
   *  be substituted for
   */
  Term register_arg(const std::string & name, const smt::Sort & sort);

 protected:
  yy::location location_;

  smt::SmtSolver solver_;

  Command
      current_command_;  ///< which smt-lib command is currently being processed

  std::unordered_map<std::string, smt::Term> symbols_;

  // define-fun data structures
  // TODO See if we can make this less complicated
  std::unordered_map<std::string, smt::Term>
      defs_;  ///< keeps track of define-funs
  std::unordered_map<std::string, smt::TermVec>
      def_args_;  ///< keeps track of define-fun
                  ///< arguments
  std::unordered_map<smt::Sort, smt::TermVec>
      tmp_args_;  ///< temporary variables
                  ///< organized by sort

  std::unordered_map<std::string, smt::Term> tmp_arg_mapping_;
  std::unordered_map<smt::Sort, std::unordered_map<std::string, smt::Term>>
      sort_tmp_arg_mapping_;

  // useful constants
  std::string def_arg_prefix_;  ///< the prefix for renamed define-fun arguments
};

} // namespace smt
