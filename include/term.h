/*********************                                                        */
/*! \file term.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Clark Barrett
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Abstract interface for SMT terms.
**
**
**/

#ifndef SMT_SWITCH_INTERNAL
// IWYU pragma: private, include "smt-switch/smt.h"
#endif

#pragma once

#include <cstddef>
#include <cstdint>
#include <iterator>
#include <list>
#include <memory>
#include <ostream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "ops.h"
#include "smt_defs.h"
#include "sort.h"

namespace smt {

class AbsTerm;
class TermIter;

namespace detail {

// Gives AbsTerm shared_from_this. Deleting a term through a base whose
// destructor is not virtual would skip the term's own destructors, and
// enable_shared_from_this's is not virtual and can be reached by its
// friend classes.
class SharedTermBase : public std::enable_shared_from_this<AbsTerm>
{
 protected:
  // Protected so no term can be deleted through it
  ~SharedTermBase() = default;
};

}  // namespace detail

// Abstract class for term
class AbsTerm : public detail::SharedTermBase
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
   *  as unsigned and must be at most 64 bits wide, whatever their value.
   */
  virtual std::uint64_t to_int() const = 0;
  /** like to_int, but signed
   *  Integer values (and real values with an integral value) must be in
   *  [INT64_MIN, INT64_MAX]; bit-vector values are read in two's
   *  complement, e.g. #b1111 is -1, and must be at most 64 bits wide.
   *  Throws an IncorrectUsageException for anything else.
   *  The default implementation parses to_string().
   */
  virtual std::int64_t to_signed_int() const;
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

 protected:
  /** Returns the number of children that begin() and end() iterate over */
  virtual std::size_t get_num_children() const = 0;
  /** Returns the child at index i
   *  @param i an index below get_num_children()
   */
  virtual Term get_child(std::size_t i) const = 0;

  friend class TermIter;
};

// A null term equals only another null term and sorts before every term
bool operator==(const Term & t1, const Term & t2);
bool operator!=(const Term & t1, const Term & t2);
bool operator<(const Term & t1, const Term & t2);
bool operator>(const Term & t1, const Term & t2);
bool operator<=(const Term & t1, const Term & t2);
bool operator>=(const Term & t1, const Term & t2);

std::ostream & operator<<(std::ostream & output, const Term t);

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

// useful typedefs for data structures
using TermVec = std::vector<Term>;
using TermList = std::list<Term>;
using UnorderedTermSet = std::unordered_set<Term>;
using UnorderedTermMap = std::unordered_map<Term, Term>;

// range-based iteration
TermIter begin(const Term & t);
TermIter end(const Term & t);

}  // namespace smt
