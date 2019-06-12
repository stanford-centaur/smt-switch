#ifndef SMT_TERM_H
#define SMT_TERM_H

#include <iostream>
#include <string>
#include <vector>

#include "smt_defs.h"

namespace smt {

class TermIter;

// Abstract class for term
class AbsTerm
{
 public:
  AbsTerm(){};
  virtual ~AbsTerm(){};
  virtual std::size_t hash() const = 0;
  // it would be nice to make this private, but then can't be called by Term
  // unless we make it a friend (which would be strange for CVC4)
  /* Should return true iff the terms are identical */
  virtual bool compare(const Term& absterm) const = 0;
  // Term methods
  virtual Fun get_fun() const = 0;
  virtual Sort get_sort() const = 0;
  virtual std::string to_string() const = 0;
  virtual uint64_t to_int() const = 0;
  virtual TermIter begin() = 0;
  virtual TermIter end() = 0;
  // TODO Add other convenient term methods
};

bool operator==(const Term& t1, const Term& t2);
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
  const virtual Term operator*() const;
  virtual TermIterBase* clone() const { return new TermIterBase(*this); }
  bool operator==(const TermIterBase& other) const;

 protected:
  // TODO: should we make this pure virtual instead? needs to be implemented
  //       but then we'd have to use pointers for everything...
  virtual bool equal(const TermIterBase& other) const { return true; }
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
  Term operator*() const { return *(*iter_); }
  bool operator==(const TermIter& other) const;
  bool operator!=(const TermIter& other) const;

 protected:
  TermIterBase* iter_;
};

}  // namespace smt

#endif
