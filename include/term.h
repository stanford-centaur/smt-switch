#ifndef SMT_TERM_H
#define SMT_TERM_H

#include "sort.h"
#include <iostream>
#include <memory>
#include <string>

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
    virtual std::vector<shared_ptr<AbsTerm>> getChildren() const = 0;
    virtual Sort getSort() const = 0;
    virtual std::string toString() const = 0;

    // TODO Add other convenient term methods
  };

  using Term=shared_ptr<AbsTerm>;
}

#endif
