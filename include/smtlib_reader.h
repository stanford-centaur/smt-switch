/*********************                                                        */
/*! \file smtlib_reader.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Driver for reading SMT-LIB files. Depends on flex/bison
**
**
**/

#pragma once

#include "assert.h"
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
  UnorderedScopedSymbolMap()
  {
    // allow some symbols at 0
    symbols_.push_back({});
  }

  size_t current_scope() { return symbols_.size() - 1; }

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

  /** Looks up symbol in the symbol map
   *  @param sym the symbol to look up
   *  @return the associated term or null pointer if not in map
   */
  smt::Term get_symbol(const std::string & sym)
  {
    Term res;
    auto it = symbol_map_.find(sym);
    if (it != symbol_map_.end())
    {
      res = it->second;
    }
    return res;
  }

 private:
  std::vector<std::unordered_set<std::string>> symbols_;
  std::unordered_map<std::string, smt::Term> symbol_map_;
};

class SmtLibReader
{
 public:
  /**
   *  Constructs an SmtLibReader which will exercise
   *  the given solver
   *  @param solver the solver to use
   *  @param strict if set to true strictly interprets SMT-LIB semantics
   *         otherwise allows non-standard operators
   */
  SmtLibReader(smt::SmtSolver & solver, bool strict = false);

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

  /** Pushes num contexts in the solver and the global symbol map
   *  If overriding, make sure to push scopes in global_symbols_
   *    or consider calling this version of the function also
   */
  virtual void push(uint64_t num = 1);

  /** Pops num contexts in the solver and the global symbol map
   *  If overriding, make sure to pop scopes in global_symbols_
   *    or consider calling this version of the function also
   */
  virtual void pop(uint64_t num = 1);

  /* getters and setters  */
  yy::location & location() { return location_; }

  smt::SmtSolver & solver() { return solver_; }

  bool is_strict() const { return strict_; }

  /** Pushes a scope for a new quantifier binding or define-fun arguments
   */
  void push_scope();

  /** Pushes a scope from quantifier binding or define-fun arguments
   */
  void pop_scope();

  size_t current_scope() { return arg_param_map_.current_scope(); }

  /* Methods for use in flex/bison generated code */

  /** Look up a symbol by name
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
   *  Returns NUM_OPS_AND_NULL if there's no match
   */
  PrimOp lookup_primop(const std::string & str);

  /** Look up a sort by string
   *  The available sorts are based on the logic
   *  @param str the string to look up
   *  @return a sort
   *  Returns NUM_SORT_KINDS (a null element) if there's
   *  no match
   */
  smt::SortKind lookup_sortkind(const std::string & str);

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

  /** Create an alias for a sort
   *  define-sort in SMT-LIB can take arguments, but currently this
   *  only supports 0-arity defined sorts
   *  It also is currently not scoped correctly
   *  TODO fix these limitations
   *  @param name the name of the defined sort
   *  @param sort the sort to associate name with
   */
  void define_sort(const std::string & name,
                   const smt::Sort & sort);

  /** Looks up a defined sort by name
   *  @param name the name to look up
   *  @return the sort
   */
  smt::Sort lookup_sort(const std::string & name);

  /** Creates a parameter and stores it in the scoped data-structure
   *  arg_param_map_
   *  parameters are variables to be bound by a quantifier
   *  @param name the name of the parameter
   *  @param sort the sort of the parameter
   *  @return the parameter
   */
  Term create_param(const std::string & name, const smt::Sort & sort);

  /** Declare a let binding mapping a symbol to a term
   *  for the current scope
   *  @param sym the symbol
   *  @param term the term
   */
  void let_binding(const std::string & sym, const smt::Term & term);

 protected:
  yy::location location_;

  smt::SmtSolver solver_;

  bool strict_;

  std::string logic_;

  std::unordered_map<std::string, smt::PrimOp>
      primops_;  ///< available primops with set logic

  std::unordered_map<std::string, smt::SortKind>
      sortkinds_;  ///< available sortkinds with set logic

  std::unordered_map<std::string, smt::Term>
      all_symbols_;  ///< remembers all symbolic constants
                     ///< and functions
                     ///< even after context is popped

  std::unordered_map<std::string, smt::Sort>
    defined_sorts_; ///< mapping from symbol to defined sort
                    ///< currently only supports 0-arity defines

  UnorderedScopedSymbolMap
      global_symbols_;  ///< symbolic constants and functions
                        ///< defined functions with no arguments
                        ///< scoped by the solver context
                        ///< e.g. push / pop

  UnorderedScopedSymbolMap
      arg_param_map_;  ///< map for arguments (to define-funs)
                       ///< and parameters (bound variables)
                       ///< scoped by the term structure
                       ///< e.g. nested quantifiers

  // define-fun data structures
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

  // useful constants
  std::string def_arg_prefix_;  ///< the prefix for renamed define-fun arguments
};

}  // namespace smt
