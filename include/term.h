#ifndef SMT_TERM_H
#define SMT_TERM_H

#include <iostream>
#include <iterator>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "ops.h"
#include "smt_defs.h"
#include "sort.h"

namespace smt {

class TermIter;

// Abstract class for term
class AbsTerm
{
 public:
  AbsTerm(){};
  virtual ~AbsTerm(){};
  virtual std::size_t hash() const = 0;
  /* Should return true iff the terms are identical */
  virtual bool compare(const Term& absterm) const = 0;
  // Term methods
  /* get the Op used to create this term */
  virtual Op get_op() const = 0;
  /* get the sort */
  virtual Sort get_sort() const = 0;
  /* to_string in smt2 format */
  virtual std::string to_string() = 0;
  /* returns true iff this term is a symbolic constant */
  virtual bool is_symbolic_const() const = 0;
  /* returns true iff this term is an interpreted constant */
  virtual bool is_value() const = 0;
  /** converts a constant that can be represented as an int to an int
   *  otherwise, throws an IncorrectUsageException
   */
  virtual uint64_t to_int() const = 0;
  /** begin iterator
   *  starts iteration through Term's children
   */
  virtual TermIter begin() = 0;
  /** end iterator
   *  ends iteration through Term's children
   */
  virtual TermIter end() = 0;

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
  virtual std::string print_value_as(SortKind sk) = 0;
};

bool operator==(const Term& t1, const Term& t2);
bool operator!=(const Term & t1, const Term & t2);
std::ostream& operator<<(std::ostream& output, const Term t);

// term iterators
// impelementation based on
// https://www.codeproject.com/Articles/92671/How-to-write-abstract-iterators-in-Cplusplus
class TermIterBase
{
 public:
  TermIterBase() {}
  virtual ~TermIterBase() {}
  virtual void operator++() {}
  const virtual Term operator*();
  virtual TermIterBase * clone() const = 0;
  bool operator==(const TermIterBase& other) const;

 protected:
  virtual bool equal(const TermIterBase & other) const = 0;
};

class TermIter
{
 public:
  // typedefs for marking as an input iterator
  // based on iterator_traits: https://en.cppreference.com/w/cpp/iterator/iterator_traits
  // used by the compiler for statements such as: TermVec children(term->begin(), term->end())
  typedef Term value_type;
  typedef std::ptrdiff_t difference_type;
  typedef Term * pointer;
  typedef Term & reference;
  typedef std::input_iterator_tag iterator_category;

  TermIter() : iter_(0) {}
  TermIter(TermIterBase* tib) : iter_(tib) {}
  ~TermIter() { delete iter_; }
  TermIter(const TermIter& other) : iter_(other.iter_->clone()) {}
  TermIter& operator=(const TermIter& other);
  TermIter& operator++();
  TermIter operator++(int junk);
  Term operator*() const { return *(*iter_); }
  bool operator==(const TermIter& other) const;
  bool operator!=(const TermIter& other) const;

 protected:
  TermIterBase* iter_;
};

// useful typedefs for data structures
using TermVec = std::vector<Term>;
using UnorderedTermSet = std::unordered_set<Term>;
using UnorderedTermMap = std::unordered_map<Term, Term>;
// range-based iteration
inline TermIter begin(Term & t) { return t->begin(); }
inline TermIter end(Term & t) { return t->end(); }

}  // namespace smt

namespace std
{
  // Specialize the hash function for data structures
  template<>
  struct hash<smt::Term>
  {
    size_t operator()(const smt::Term & t) const
    {
      return t->hash();
    }
  };
}

#endif
