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

#include <cstddef>
#include <cstdint>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "exceptions.h"
#include "ops.h"
#include "result.h"
#include "smt_defs.h"
#include "sort.h"
#include "term.h"

/** Thrown when SmtLibReader cannot parse its input: a syntax error, a
 *  symbol, sort or character it does not know, or something it or the
 *  solver refuses, such as a redeclaration. The message starts with where,
 *  as file:line.column.
 */
class SmtLibParseException : public SmtException
{
 public:
  using SmtException::SmtException;
  // defined in the .cpp to anchor the vtable
  ~SmtLibParseException() override;
};

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
  std::size_t current_scope() const;

  void add_mapping(const std::string & sym, const Term & t);

  void push_scope();

  void pop_scope();

  /** Looks up symbol in the symbol map
   *  @param sym the symbol to look up
   *  @return the associated term or null pointer if not in map
   */
  Term get_symbol(const std::string & sym) const;

 private:
  // starts with one scope, to allow some symbols at 0
  std::vector<std::unordered_set<std::string>> symbols_ = { {} };
  std::unordered_map<std::string, Term> symbol_map_;
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
  explicit SmtLibReader(SmtSolver & solver, bool strict = false);
  SmtLibReader(const SmtLibReader &) = delete;
  SmtLibReader & operator=(const SmtLibReader &) = delete;

  virtual ~SmtLibReader() = default;

  /** Parses an SMT-LIB file, running its commands
   *  @param f the file's path, or "-" or the empty string for stdin
   *  @throws IncorrectUsageException if the file cannot be opened
   *  @throws SmtLibParseException if the input cannot be parsed
   *  @throws std::runtime_error if the scanner fails, as when reading the
   *          input or allocating memory
   */
  void parse(const std::string & f);
  // The name of the file being parsed.
  std::string file;

  /* Override-able functions corresponding to SMT-LIB commands */

  virtual void set_logic(const std::string & logic);

  /** Adds all known logics */
  virtual void set_logic_all();

  virtual void set_opt(const std::string & key, const std::string & val);

  virtual void set_info(const std::string & key, const std::string & val);

  virtual void assert_formula(const Term & assertion);

  virtual Result check_sat();

  virtual Result check_sat_assuming(const TermVec & assumptions);

  /** Pushes num contexts in the solver and the global symbol map
   *  If overriding, make sure to push scopes in global_symbols_
   *    or consider calling this version of the function also
   */
  virtual void push(std::uint64_t num = 1);

  /** Pops num contexts in the solver and the global symbol map
   *  If overriding, make sure to pop scopes in global_symbols_
   *    or consider calling this version of the function also
   */
  virtual void pop(std::uint64_t num = 1);

  /** Mark a term with an attribute
   *  This currently is ignores the attribute and prints a warning.
   *  It can be overridden in a derived class to do something
   *  useful with the attribute.
   *  @param term the term marked with an attribute
   *  @param keyword the attribute keyword
   *  @param value the attribute value
   */
  virtual void term_attribute(const Term & term,
                              const std::string & keyword,
                              const std::string & value);

  /* Getters and setters */
  const SmtSolver & solver() const;

  bool is_strict() const;

  /** Pushes a scope for a new quantifier binding or define-fun arguments
   */
  void push_scope();

  /** Pushes a scope from quantifier binding or define-fun arguments
   */
  void pop_scope();

  std::size_t current_scope() const;

  /* Methods for use in flex/bison generated code */

  /** Look up a symbol by name
   *  Returns a null term if there is no known symbol
   *  with that name
   *  @return term
   */
  Term lookup_symbol(const std::string & sym) const;

  /** Creates a new symbol
   *  This is a light wrapper around solver_->make_symbol
   *  s.t. you can look up the symbol by name later
   *  see lookup_symbol
   *  @param name the name of the symbol
   *  @param sort the sort of the symbol
   */
  virtual void new_symbol(const std::string & name, const Sort & sort);

  /** Look up a primitive operator by a string
   *  @param str the string representation of this PrimOp
   *  @return the associated PrimOp
   *  Returns NUM_OPS_AND_NULL if there's no match
   */
  PrimOp lookup_primop(const std::string & str) const;

  /** Apply a primitive operator to its arguments, where unary - is the
   *  negation. In a logic of both Ints and Reals, an operator over Reals
   *  takes an Int argument next to a Real one as a Real, and / takes every
   *  Int argument as one, as the SMT-LIB logic AUFLIRA defines it. Outside
   *  strict mode, so do = and distinct.
   *  @param po the operator
   *  @param args its arguments
   *  @return the application
   */
  Term apply_primop(PrimOp po, TermVec args) const;

  /** Look up a sort by string
   *  The available sorts are based on the logic
   *  @param str the string to look up
   *  @return a sort
   *  Returns NUM_SORT_KINDS (a null element) if there's
   *  no match
   */
  SortKind lookup_sortkind(const std::string & str) const;

  /** Create a define-fun macro
   *  @param name the name of the define-fun
   *  @param the definition
   *  @param the arguments to the define-fun
   *  stored in defs_ and def_args_
   */
  void define_fun(const std::string & name,
                  const Term & def,
                  const TermVec & args = {});

  /** Apply a define fun
   *  @param defname the name of the define-fun
   *  @param args the arguments to apply it to
   *         the parameter args from the define-fun
   *         declaration will be replaced by these arguments
   */
  Term apply_define_fun(const std::string & defname, const TermVec & args);

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
  Term register_arg(const std::string & name, const Sort & sort);

  /** Create an alias for a sort
   *  define-sort in SMT-LIB can take arguments, but currently this
   *  only supports 0-arity defined sorts
   *  It also is currently not scoped correctly
   *  TODO fix these limitations
   *  @param name the name of the defined sort
   *  @param sort the sort to associate name with
   */
  void define_sort(const std::string & name, const Sort & sort);

  /** Looks up a defined sort by name
   *  @param name the name to look up
   *  @return the sort
   */
  Sort lookup_sort(const std::string & name) const;

  /** Creates a parameter and stores it in the scoped data-structure
   *  arg_param_map_
   *  parameters are variables to be bound by a quantifier
   *  @param name the name of the parameter
   *  @param sort the sort of the parameter
   *  @return the parameter
   */
  Term create_param(const std::string & name, const Sort & sort);

  /** Declare a let binding mapping a symbol to a term
   *  for the current scope
   *  @param sym the symbol
   *  @param term the term
   */
  void let_binding(const std::string & sym, const Term & term);

 protected:
  SmtSolver solver_;

  bool strict_;

  std::string logic_ = "UNSET";  ///< holds the logic string

  bool allow_ufs_ = false;  ///< set to true if declaring functions
                            ///< is supported in the set logic

  std::unordered_map<std::string, PrimOp>
      primops_;  ///< available primops with set logic

  std::unordered_map<std::string, SortKind>
      sortkinds_;  ///< available sortkinds with set logic

  std::unordered_map<std::string, Term>
      all_symbols_;  ///< remembers all symbolic constants
                     ///< and functions
                     ///< even after context is popped

  std::unordered_map<std::string, Sort>
      defined_sorts_;  ///< mapping from symbol to defined sort
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
  std::unordered_map<std::string, Term> defs_;  ///< keeps track of define-funs
  std::unordered_map<std::string, TermVec>
      def_args_;  ///< keeps track of define-fun arguments
  std::unordered_map<Sort, TermVec>
      tmp_args_;  ///< temporary variables organized by sort
  std::vector<std::unordered_map<Sort, std::size_t>>
      sort_arg_ids_;  ///< scope-dependent argument ids in use
                      ///< example: sort_arg_ids_.back()[intsort]
                      ///< returns the first index into tmp_args (might be out
                      ///< of bounds, which means a new tmp argument is needed)
                      ///< that is currently unused in this scope

  // useful constants
  std::string def_arg_prefix_ = "__defvar_";  ///< the prefix for renamed
                                              ///< define-fun arguments
};

}  // namespace smt
