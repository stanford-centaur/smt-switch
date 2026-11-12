/*!
 * \file term_builder.h
 * \brief Abstract interface for building the terms and sorts of a backend
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_TERM_BUILDER_H
#define SMT_SWITCH_TERM_BUILDER_H

#ifndef SMT_SWITCH_INTERNAL
// IWYU pragma: private, include "smt-switch/smt.h"
#endif

#include <cstdint>
#include <string>
#include <type_traits>
#include <vector>

#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

namespace smt {

/**
   Builds the terms and sorts of one backend. Both a solver and an
   interpolator do.

   Terms and sorts keep alive the backend state they point into, so they can
   still be used after their term builder is destroyed.
 */
class AbsTermBuilder
{
 public:
  AbsTermBuilder() = default;
  AbsTermBuilder(const AbsTermBuilder & other) = default;
  AbsTermBuilder & operator=(const AbsTermBuilder & other) = default;
  virtual ~AbsTermBuilder() = default;

  /* Declare an uninterpreted sort, or a sort constructor if arity is nonzero
   * SMTLIB: (declare-sort <name> <arity>)
   * @param name the name of the sort
   * @param arity the arity of the sort
   * @return a Sort object
   */
  virtual Sort make_sort(const std::string name, std::uint64_t arity) const = 0;

  /* Create a sort
   * @param sk the SortKind (BOOL, INT, REAL)
   * @return a Sort object
   */
  virtual Sort make_sort(const SortKind sk) const = 0;

  /* Create a sort
   * @param sk the SortKind (BV)
   * @param size (e.g. bitvector width for BV SortKind)
   * @return a Sort object
   */
  virtual Sort make_sort(const SortKind sk, std::uint64_t size) const = 0;

  /* Create a sort from sort parameters
   * @param sk the SortKind (ARRAY, FUNCTION)
   * @param sorts for ARRAY, the index sort then the element sort; for
   * FUNCTION, the domain sorts then the codomain sort
   * @return a Sort object
   * This is the overload a backend implements; the one taking the sorts as
   * separate arguments below is a shorthand for it.
   */
  virtual Sort make_sort(const SortKind sk, const SortVec & sorts) const = 0;

  /* Shorthand for make_sort(sk, SortVec{ sort1, sorts... })
   * e.g. make_sort(ARRAY, index, element) or make_sort(FUNCTION, d1, d2, cod)
   * No SortKind takes a single sort parameter yet.
   */
  template <typename... Sorts,
            typename = std::enable_if_t<
                (std::is_convertible_v<const Sorts &, Sort> && ...)>>
  Sort make_sort(const SortKind sk,
                 const Sort & sort1,
                 const Sorts &... sorts) const
  {
    return make_sort(sk, SortVec{ sort1, sorts... });
  }

  /* Apply a sort constructor to sorts
   * SMTLIB: ( <identifier> <sort>+ ), for instance (List Int)
   * @param sort_con a sort with SortKind UNINTERPRETED_CONS (must have
   * nonzero arity)
   * @param sorts a vector of sorts of size matching sort_con->get_arity()
   * @return a Sort object
   */
  virtual Sort make_sort(const Sort & sort_con,
                         const SortVec & sorts) const = 0;

  /* Make a boolean value term
   * @param b boolean value
   * @return a value term with Sort BOOL and value b
   */
  virtual Term make_term(bool b) const = 0;

  /* Make a bit-vector, int or real value term
   * @param i the value
   * @param sort the sort to create
   * @return a value term with Sort sort and value i
   */
  virtual Term make_term(std::int64_t i, const Sort & sort) const = 0;

  /* Make a bit-vector, int, real or (in the future) string value term
   * @param val the numeric value as a string, or a string value
   * @param sort the sort to create
   * @param base the base val is written in, from 2 to 36, for the digits (0
   * to 9, then a to z in either case) of a numeral and of each part of a
   * decimal or fraction
   * @return a value term with Sort sort and value val
   */
  virtual Term make_term(const std::string val,
                         const Sort & sort,
                         std::uint64_t base = 10) const = 0;

  /* Make a value of a particular sort, such as constant arrays
   * @param val the Term used to create the value (.e.g constant array with 0)
   * @param sort the sort of value to create
   * @return a value term with Sort sort
   */
  virtual Term make_term(const Term & val, const Sort & sort) const = 0;

  /* Make a symbolic constant or function term
   * SMTLIB: (declare-fun <name> (s1 ... sn) s) where sort = s1x...xsn -> s
   * @param name the name of constant or function
   * @param sort the sort of this constant or function
   * @return the symbolic constant or function term
   */
  virtual Term make_symbol(const std::string name, const Sort & sort) = 0;

  /** Look up a symbol by name.
   *  If no symbol of that name has been declared, throws
   *  IncorrectUsageException
   *
   *  Allows a user to look up a symbol by name. This can be very useful for
   * term translation, since we can look up symbols instead of keeping track of
   * the mapping via externally populated caches (in the case where the target
   *  solver has already been used).
   *
   *  Note, solver backend deals with the implementation. The main motivation
   * for this is that each backend solver has to own the symbol table. If the
   * symbol table were stored in AbsTermBuilder then it would get destructed
   * after the backend solver which has bad refcounting implications for many
   * solvers.
   *
   *  @param name the name of the symbol to look up
   *  @return the Term representation of the corresponding symbol
   */
  virtual Term get_symbol(const std::string & name) const = 0;

  /* Make a parameter term to be bound by a quantifier
   * @param name the name of the parameter
   * @param sort the sort of this parameter
   * @return the parameter term
   */
  virtual Term make_param(const std::string name, const Sort & sort) const = 0;

  /* Make a new term
   * @param op the operator to use
   * @param terms vector of children; for Forall and Exists, the params to
   *        bind and then the body, the params bound from left to right
   * @return the created term
   * This is the overload a backend implements; the one taking the children
   * as separate arguments below is a shorthand for it.
   */
  virtual Term make_term(const Op op, const TermVec & terms) const = 0;

  /* Shorthand for make_term(op, TermVec{ t, ts... })
   * e.g. make_term(Not, a), make_term(Equal, a, b) or make_term(And, a, b, c)
   */
  template <typename... Terms,
            typename = std::enable_if_t<
                (std::is_convertible_v<const Terms &, Term> && ...)>>
  Term make_term(const Op op, const Term & t, const Terms &... ts) const
  {
    return make_term(op, TermVec{ t, ts... });
  }

  // ---------------------------- Strings ------------------------------------

  /* Make a string value term from an `std::string` which may contain SMT-LIB
   * compatible escape sequences like `\u1000` or `\u{20}` to encode unicode
   * characters.
   * @param s is the value
   * @param useEscSequences determines whether escape sequence in `s` should
   * be converted to the corresponding unicode character
   * @param sort the sort to create
   * @return a value term with Sort sort and value s
   */
  virtual Term make_term(const std::string & s,
                         bool useEscSequences,
                         const Sort & sort) const = 0;

  /* Make a string value term
   * @param s is the value
   * @param sort the sort to create
   * @return a value term with Sort sort and value s
   */
  virtual Term make_term(const std::wstring & s, const Sort & sort) const = 0;

  // --------------------------- Datatypes ----------------------------------

  /* Create a datatype sort
   * @param d the Datatype Declaration
   * @return a Sort object
   */
  virtual Sort make_sort(const DatatypeDecl & d) const = 0;

  /* Initialize a datatype declaration with some name
   * @param s Name of the datatype
   * @return an empty Datatype declaration
   */
  virtual DatatypeDecl make_datatype_decl(const std::string & s) const = 0;

  /* Initialize a datatype constructor declaration with some name
   * @param s Name of the datatype constructor
   * @return an empty Datatype declaration
   */
  virtual DatatypeConstructorDecl make_datatype_constructor_decl(
      const std::string s) const = 0;

  /* Add a datatype constructor to a datatype declaration
   * @param dt Datatype
   * @param con Datatype constructor
   */
  virtual void add_constructor(DatatypeDecl & dt,
                               const DatatypeConstructorDecl & con) const = 0;

  /* Add a selector to a datatype constructor
   * @param dt DatatypeConstructorDecl
   * @param name name of the selector
   * @param s sort of the selector
   */

  virtual void add_selector(DatatypeConstructorDecl & dt,
                            const std::string & name,
                            const Sort & s) const = 0;

  /* Add a selector to a datatype constructor where the sort is the datatype
   * itself (whose sort doesn't exist yet)
   * @param dt DatatypeConstructorDecl
   * @param name name of the selector
   */
  virtual void add_selector_self(DatatypeConstructorDecl & dt,
                                 const std::string & name) const = 0;

  /* get a term representing to a datatype constructor
   * @param s A datatype sort (error otherwise)
   * @param name name of the constructor
   */

  virtual Term get_constructor(const Sort & s, std::string name) const = 0;

  /* get a term representing to a datatype tester
   * @param s A datatype sort (error otherwise)
   * @param name name of the constructor
   */

  virtual Term get_tester(const Sort & s, std::string name) const = 0;

  /* get a term representing to a datatype selector
   * @param s A datatype sort (error otherwise)
   * @param con name of the constructor
   * @param name name of the selector
   */
  virtual Term get_selector(const Sort & s,
                            std::string con,
                            std::string name) const = 0;

  /** Create sorts for the corresponding DatatypeDecls.
   *
   *  @param decls the datatype decls
   *  @return one datatype sort per declaration, in the same order
   */
  virtual SortVec make_datatype_sorts(
      const std::vector<DatatypeDecl> & decls) const = 0;

  /** Convenience function that calls make_datatype_sorts with a single sort. */
  Sort make_datatype_sort(const DatatypeDecl & decl) const;

  // Methods implemented at the abstract level
  // Note: These can be overridden in the specific solver implementation for
  //       performance improvements

  /** Replaces each key of substitution_map in term with its value. A key
   *  can be any term, and is replaced whole wherever it occurs; the values
   *  are not substituted in turn.
   * @param term the term to apply substitution map to
   * @param substitution_map the map to use for substitution
   * @return the term with the substitution map applied
   * @throws NotImplementedException for a key other than a symbol or param
   *         where the solver's terms need not contain it as built
   */
  virtual Term substitute(const Term term,
                          const UnorderedTermMap & substitution_map) const;

  /** substitute applied to each of terms
   * @return the results, in the order of terms
   */
  virtual TermVec substitute_terms(
      const TermVec & terms, const UnorderedTermMap & substitution_map) const;

  // Casts of terms between Bool and bit-vectors and between Int and Real,
  // defined in term_casts.cpp

  /** A term as another sort, between Bool and bit-vectors or between Int and
   *  Real. A bit-vector is true when it equals 1; a value cast between Bool
   *  and a bit-vector must have width one.
   *  @param term the term to cast
   *  @param sort the sort to cast it to
   *  @return term itself if it has that sort already, else a term of sort
   *  @throws NotImplementedException for any other pair of sorts
   */
  Term cast_term(const Term & term, const Sort & sort) const;

  /** An operator applied to terms, cast where the operator does not accept
   *  them as they are: the terms are cast as cast_term does, or the operator
   *  is swapped for its Boolean or bit-vector counterpart, such as And for
   *  BVAnd
   *  @param op the operator
   *  @param terms the terms to apply it to
   *  @return a well-sorted application of op or its counterpart
   *  @throws NotImplementedException if no such cast makes it well sorted
   *  @throws IncorrectUsageException for a function applied to the wrong
   *          number of arguments
   */
  Term cast_op(const Op & op, const TermVec & terms) const;
};

}  // namespace smt

#endif  // SMT_SWITCH_TERM_BUILDER_H
