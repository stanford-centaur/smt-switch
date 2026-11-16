/*!
 * \file term.h
 * \brief Abstract interface for SMT terms
 * \author Makai Mann
 * \author Clark Barrett
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_TERM_H
#define SMT_SWITCH_TERM_H

#ifndef SMT_SWITCH_INTERNAL
// IWYU pragma: private, include "smt-switch/smt.h"
#endif

#include <cstddef>
#include <cstdint>
#include <iterator>
#include <memory>
#include <string>
#include <unordered_set>

#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"

namespace smt {

class TermIter;

// Abstract class for term
class AbsTerm : public internal::SharedBase<AbsTerm>
{
 public:
  virtual ~AbsTerm() = default;
  /** Returns a hash for this term */
  virtual std::size_t hash() const = 0;
  /** Returns a unique id for this term */
  virtual std::size_t get_id() const = 0;
  /* Should return true iff the terms are identical */
  virtual bool compare(const Term & absterm) const = 0;
  // Term methods
  /* get the Op used to create this term */
  virtual Op get_op() const = 0;
  /* get the sort */
  virtual Sort get_sort() const = 0;
  /* to_string in smt2 format */
  virtual std::string to_string() const = 0;
  /* returns the string term as a native string value */
  virtual std::wstring getStringValue() const;
  /* returns true iff this term is a symbol */
  virtual bool is_symbol() const = 0;
  /* returns true iff this term is a parameter (to be bound by a quantifier) */
  virtual bool is_param() const = 0;
  /* returns true iff this term is a symbolic constant */
  virtual bool is_symbolic_const() const = 0;
  /** Returns true iff this term is a value: a literal, an abstract value, a
   *  constant array, or a datatype constructor applied to values. No symbol
   *  is a value, not even a function.
   */
  virtual bool is_value() const = 0;
  /** Returns the name a constructor was declared with, or that of the
   *  constructor a tester tests, unquoted.
   *  Throws an IncorrectUsageException unless the term is a constructor or a
   *  tester.
   */
  virtual std::string get_constructor_name() const = 0;
  /** Returns the name the param was made with, unquoted.
   *  Throws an IncorrectUsageException unless the term is a param.
   */
  virtual std::string get_param_name() const = 0;
  /** Returns the name the selector was declared with, unquoted.
   *  Throws an IncorrectUsageException unless the term is a selector.
   */
  virtual std::string get_selector_name() const = 0;
  /** Returns the name the symbol was made with. Unlike to_string, which
   *  prints SMT-LIB, it is never quoted: a symbol made as "a b" is named
   *  a b, not |a b|.
   *  Throws an IncorrectUsageException unless the term is a symbol that is
   *  not a parameter.
   */
  virtual std::string get_symbol_name() const = 0;
  /** converts a value that can be represented as an int to an int
   *  otherwise, throws an IncorrectUsageException
   *  Integer values (and real values with an integral value) must be in
   *  [0, UINT64_MAX], so a negative one, which SMT-LIB writes as (- n),
   *  throws; read it with to_signed_int instead. Bit-vector values are read
   *  as unsigned and must be at most UINT64_MAX, whatever their width.
   */
  virtual std::uint64_t to_int() const = 0;
  /** like to_int, but signed
   *  Integer values (and real values with an integral value) must be in
   *  [INT64_MIN, INT64_MAX]; bit-vector values are read in two's
   *  complement of their width, e.g. #b1111 is -1, and must be in
   *  [INT64_MIN, INT64_MAX] too, whatever their width.
   *  Throws an IncorrectUsageException for anything else.
   *  The default implementation parses to_string().
   */
  virtual std::int64_t to_signed_int() const;
  /** Returns the bits of a bit-vector value, most significant first, as
   *  many as its width.
   *  Throws an IncorrectUsageException for anything else.
   *  The default implementation parses to_string().
   */
  virtual std::string to_bits() const;
  /** Returns the value of a Boolean value.
   *  On a solver with BOOL_BV1_ALIASING, a 1-bit bit-vector value is a
   *  Boolean value too, and #b1 is true.
   *  Throws an IncorrectUsageException for anything else.
   *  The default implementation parses to_string().
   */
  virtual bool to_bool() const;
  /** begin iterator
   *  starts iteration through Term's children
   */
  TermIter begin() const;
  /** end iterator
   *  ends iteration through Term's children
   */
  TermIter end() const;

  // Methods used for strange edge-cases e.g. in the logging solver

  /** Print a value term in a specific form
   *  NOTE: this *only* exists for use in LoggingSolver
   *        it is to handle printing of values from solvers that alias
   *        sorts. For example, if Bool and (_ BitVec 1) are aliased,
   *        this can be used to print #b1 as true.
   *
   *  This method canNOT be used to convert arbitrarily, e.g.
   *  it cannot print a bitvector as an integer.
   *
   *  Thus, solvers that don't alias sorts can just use their to_string
   *  to implement this method
   *
   *  @param sk the SortKind to print the term as
   *  @param a string representation of the term
   *
   *  throws an exception if the term is not a value
   */
  virtual std::string print_value_as(SortKind sk) const = 0;

  // Queries of this term and its subterms

  /** Collects the terms where the applications of o from this term down
   *  stop: the arguments of the outermost application of o, split again where
   *  they apply o themselves
   *  @param o the operator
   *  @param out the vector the terms are added to
   */
  void op_partition(PrimOp o, TermVec & out);

  /** Populates a vector with conjuncts from a term
   *  @param out the output vector
   *  @param include_bvand also split on BVAnd over 1-bit signals
   *         Note: this is mainly for use with Boolector which treats
   *         booleans as 1-bit bit-vectors. Using this option on a term
   *         that is known to be boolean will give you the expected
   *         partition.
   */
  void conjunctive_partition(TermVec & out, bool include_bvand = false);

  /** Populates a vector with disjuncts from a term
   *  @param out the output vector
   *  @param include_bvor also split on BVOr over 1-bit signals
   */
  void disjunctive_partition(TermVec & out, bool include_bvor = false);

  void get_matching_terms(UnorderedTermSet & out,
                          bool (*matching_fun)(const Term & term));

  void get_free_symbolic_consts(UnorderedTermSet & out);

  void get_free_symbols(UnorderedTermSet & out);

  void get_ops(std::unordered_set<Op> & out);

  /** Collects the subterms built with any of the given operators, including
   *  those below another one
   *  @param ops the operators to look for
   *  @param out the set the subterms are added to
   */
  void get_terms_with_ops(const std::unordered_set<PrimOp> & ops,
                          UnorderedTermSet & out);

  /** returns true iff this term is a literal
   *  e.g. either a boolean symbolic constant or its negation
   *  NOTE will return false for nested negations, i.e. (not (not (not l)))
   *  @param boolsort a boolean sort from the corresponding solver
   *         this way sort aliasing solvers are still supported
   *  @return true iff this term is a literal
   */
  bool is_lit(const Sort & boolsort);

  /** Whether this term is a theory atom: a Boolean application other than a
   *  connective, a quantifier, an extract, or an equality or distinct over
   *  Booleans. Symbols and values are not theory atoms.
   *  @param boolsort the Boolean sort of the term's solver, so that solvers
   * that alias Booleans and bit-vectors of width one are supported
   *  @return true iff this term is a theory atom
   */
  bool is_theory_atom(const Sort & boolsort);

 protected:
  /** Returns the number of children that begin() and end() iterate over */
  virtual std::size_t get_num_children() const = 0;
  /** Returns the child at index i
   *  @param i an index below get_num_children()
   */
  virtual Term get_child(std::size_t i) const = 0;

  // Helpers for implementing to_int, to_signed_int and to_bits, defined in
  // numeral_utils.cpp. Each throws an IncorrectUsageException if its input is
  // malformed or its value does not fit in the result type.

  /** Interprets a string of 0s and 1s, most significant bit first, as an
   *  unsigned bit-vector of the string's length, which may be any
   */
  static std::uint64_t bits_to_uint64(const std::string & bits);

  /** Interprets a string of 0s and 1s, most significant bit first, as a
   *  bit-vector in two's complement of the string's length, which may be any
   */
  static std::int64_t bits_to_int64(const std::string & bits);

  friend class TermIter;
};

// iterates over a term's children, keeping the term alive
class TermIter
{
 public:
  // typedefs for marking as an input iterator
  // based on iterator_traits:
  // https://en.cppreference.com/w/cpp/iterator/iterator_traits
  // used by the compiler for statements such as:
  // TermVec children(term->begin(), term->end())
  typedef Term value_type;
  typedef std::ptrdiff_t difference_type;
  typedef Term * pointer;
  typedef Term & reference;
  typedef std::input_iterator_tag iterator_category;

  TermIter() = default;
  TermIter(const TermIter & other) = default;
  TermIter(TermIter && other) noexcept = default;
  TermIter & operator=(const TermIter & other) = default;
  TermIter & operator=(TermIter && other) noexcept = default;
  /** @throws IncorrectUsageException on a default-constructed iterator */
  TermIter & operator++();
  /** @throws IncorrectUsageException on a default-constructed iterator */
  TermIter operator++(int junk);
  /** @throws IncorrectUsageException on a default-constructed iterator, or
   *  at or past the end of the children
   */
  Term operator*() const;
  /** Iterators are equal when both are default-constructed, or when they
   *  are over the same term object and at the same position
   */
  bool operator==(const TermIter & other) const;
  bool operator!=(const TermIter & other) const;

 private:
  TermIter(std::shared_ptr<const AbsTerm> t,
           std::size_t position,
           std::size_t size);

  std::shared_ptr<const AbsTerm> term = nullptr;
  std::size_t position = 0;
  std::size_t size = 0;

  friend class AbsTerm;
};

// range-based iteration
TermIter begin(const Term & t);
TermIter end(const Term & t);

}  // namespace smt

#endif  // SMT_SWITCH_TERM_H
