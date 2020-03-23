#ifndef SMT_TERM_H
#define SMT_TERM_H

#include <iostream>
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
  virtual std::string to_string() const = 0;
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
  // TODO Add other convenient term methods
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
