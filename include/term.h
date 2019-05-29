#ifndef SMT_TERM_H
#define SMT_TERM_H

#include <iostream>
#include <memory>
#include <string>

#include "func.h"
#include "sort.h"

namespace smt
{
  // forward declaration
  class TermIter;

  // abstract class for term
  class AbsTerm
  {
  public:
    AbsTerm() {};
    virtual ~AbsTerm() {};
    virtual std::size_t hash() const = 0;
    // it would be nice to make this private, but then can't be called by Term
    // unless we make it a friend (which would be strange for CVC4)
    /* Should return true iff the terms are identical */
    virtual bool compare(const std::shared_ptr<AbsTerm>& absterm) const = 0;
    // Term methods
    virtual std::vector<std::shared_ptr<AbsTerm>> get_children() const = 0;
    virtual Func get_func() const = 0;
    virtual std::shared_ptr<AbsSort> get_sort() const = 0;
    virtual std::string to_string() const = 0;
    virtual std::string as_bitstr() const = 0;
    virtual TermIter begin() = 0;
    virtual TermIter end() = 0;
    // TODO Add other convenient term methods
  };

  using Term=std::shared_ptr<AbsTerm>;

  bool operator==(const Term& t1, const Term& t2)
  {
   return t1->compare(t2);
  }

  std::ostream & operator<<(std::ostream & output, const Term t)
  {
   output << t->to_string();
   return output;
  }

  // term iterators
  // impelementation based on https://www.codeproject.com/Articles/92671/How-to-write-abstract-iterators-in-Cplusplus
  // TODO: Figure out who is responsible for deleting the pointer to TermIterBase
  class TermIterBase
  {
  public:
    TermIterBase() {}
    virtual ~TermIterBase() {}
    virtual void operator++() {}
    const virtual Term operator*() const { std::shared_ptr<AbsTerm> s; return s; }
    virtual TermIterBase* clone() const { return new TermIterBase(*this); }
    bool operator==(const TermIterBase& other) const
    {
     return (typeid(*this) == typeid(other)) && equal(other);
    }
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
    TermIter& operator=(const TermIter& other)
    {
     delete iter_;
     iter_ = other.iter_->clone();
     return *this;
    }
    TermIter& operator++()
    {
      ++(*iter_);
      return *this;
    }
    Term operator*() const { return *(*iter_); }
    bool operator==(const TermIter& other) const
    {
     return (iter_ == other.iter_) || (*iter_ == *other.iter_);
    }
    bool operator!=(const TermIter& other) const
    {
     return !(*this == other);
    }
  protected:
    TermIterBase * iter_;
  };

}

#endif
