#ifndef SMT_TERM_H
#define SMT_TERM_H

#include <iostream>
#include <memory>
#include <string>

#include "sort.h"

namespace smt
{

  // abstract class
  class AbsTerm
  {
  public:
    AbsTerm() {};
    virtual ~AbsTerm() {};
    virtual std::size_t hash() const = 0;
    // it would be nice to make this private, but then can't be called by Term
    // unless we make it a friend (which would be strange for CVC4)
    /* Should return true iff the terms are identical */
    virtual bool compare(AbsTerm* absterm) const = 0;
    // Term methods
    virtual std::vector<shared_ptr<AbsTerm>> get_children() const = 0;
    virtual std::shared_ptr<AbsSort> get_sort() const = 0;
    virtual std::string to_string() const = 0;

    // TODO Add other convenient term methods
  };

  using Term=shared_ptr<AbsTerm>;
}

#endif
