#pragma once

#include <string>
#include <unordered_map>

#include "smt.h"
#include "smtlibparser.h"

#define YY_DECL yy::parser::symbol_type yylex(smt::SmtLibReader & drv)
YY_DECL;

namespace smt {

/** Used to keep track of which command is currently being parsed */
enum Command
{
  SETLOGIC = 0,
  SETOPT,
  SETINFO,
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

/** Basic scoped symbol map
 *  Used for arguments and parameters that have limited scope
 *  Does not support shadowing within the same mapping scope
 *    e.g. forall x . P(x) -> exists x. Q(x)
 *    is not supported
 */
class UnorderedScopedSymbolMap
{
 public:
  size_t current_scope() { return symbols_.size(); }

  void add_mapping(const std::string & sym, const smt::Term & t)
  {
    if (symbol_map_.find(sym) != symbol_map_.end())
    {
      throw SmtException("Repeated symbol: " + sym);
    }
    symbol_map_[sym] = t;
    symbols_.back().insert(sym);
  }

  void push_scope() { symbols_.push_back({}); }

  void pop_scope()
  {
    assert(current_scope());
    for (const auto & sym : symbols_.back())
    {
      symbol_map_.erase(sym);
    }
    symbols_.pop_back();
  }

  smt::Term get_symbol(const std::string & sym) { return symbol_map_.at(sym); }

 private:
  std::vector<std::unordered_set<std::string>> symbols_;
  std::unordered_map<std::string, smt::Term> symbol_map_;
};

// TODO: remove if never used
Command str_to_command(std::string cmd);

class SmtLibReader
{
 public:
  SmtLibReader(smt::SmtSolver & solver);

  int parse(const std::string & f);
  // The name of the file being parsed.
  std::string file;

  void scan_begin();
  void scan_end();

  /* Override-able functions corresponding to SMT-LIB commands */

  virtual void set_logic(const std::string & logic);

  virtual void set_opt(const std::string & key, const std::string & val);

  virtual void set_info(const std::string & key, const std::string & val);

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

  void push_scope();

  void pop_scope();

  size_t current_scope() { return arg_param_map_.current_scope(); }

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

  Term create_param(const std::string & name, const smt::Sort & sort);

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
  std::vector<std::unordered_map<smt::Sort, size_t>>
      sort_arg_ids_;  ///< scope-dependent argument ids in use
                      ///< example: sort_arg_ids_.back()[intsort]
                      ///< returns the first index into tmp_args
                      ///< (might be out of bounds, which means a new
                      ///<  tmp argument is needed)
                      ///< that is currently unused in this scope

  UnorderedScopedSymbolMap
      arg_param_map_;  ///< map for arguments (to define-funs)
                       ///< and parameters (bound variables)

  // useful constants
  std::string def_arg_prefix_;  ///< the prefix for renamed define-fun arguments
};

}  // namespace smt
