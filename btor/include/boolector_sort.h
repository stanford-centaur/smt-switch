#ifndef SMT_BOOLECTOR_SORT_H
#define SMT_BOOLECTOR_SORT_H

#include "exceptions.h"
#include "sort.h"
#include "utils.h"

#include "boolector.h"

namespace smt {

// forward declaration
class BoolectorSolver;

class BoolectorSortBase : public AbsSort
{
 public:
  BoolectorSortBase(SortCon sc, Btor * b, BoolectorSort s)
    : btor(b), sort(s), sc(sc) {};
  virtual ~BoolectorSortBase();
  // by default none of these work
  std::string to_string() const override;
  unsigned int get_width() const override;
  Sort get_indexsort() const override;
  Sort get_elemsort() const override;
  std::vector<Sort> get_domain_sorts() const override;
  Sort get_codomain_sort() const override;
  bool compare(const Sort s) const override;
  SortCon get_sort_con() const override { return sc; };

 protected:
  Btor * btor;
  BoolectorSort sort;
  SortCon sc;

  friend class BoolectorSolver;
};

/** The Boolector C API doesn't support querying sorts for width, etc...
    (in Boolector asking for the width is done on a node, i.e. Term, rather than
   a sort) Thus, we need to track some extra information for implementing
   AbsSort. To make this simpler, we have unique classes for each sort.
 */

class BoolectorBVSort : public BoolectorSortBase
{
 public:
  BoolectorBVSort(Btor * b, BoolectorSort s, unsigned int w)
      : BoolectorSortBase(BV, b, s), width(w){};
  unsigned int get_width() const override { return width; };

 protected:
  // bit-vector width
  // Note: we need to store this in addition to the BoolectorSort
  //       because in Boolector the width is retrieved from a node not a sort
  unsigned width;

  friend class BoolectorSolver;
};

class BoolectorArraySort : public BoolectorSortBase
{
 public:
  BoolectorArraySort(Btor * b, BoolectorSort s, Sort is, Sort es)
    : BoolectorSortBase(ARRAY, b, s), indexsort(is), elemsort(es) {};
  Sort get_indexsort() const override { return indexsort; };
  Sort get_elemsort() const override { return elemsort; };

 protected:
  Sort indexsort;
  Sort elemsort;

  friend class BoolectorSolver;
};

class BoolectorUFSort : public BoolectorSortBase
{
 public:
  BoolectorUFSort(Btor * b, BoolectorSort s, std::vector<Sort> sorts, Sort sort)
      : BoolectorSortBase(FUNCTION, b, s),
        domain_sorts(sorts),
        codomain_sort(sort){};
  std::vector<Sort> get_domain_sorts() const override { return domain_sorts; };
  Sort get_codomain_sort() const override { return codomain_sort; };

 protected:
  std::vector<Sort> domain_sorts;
  Sort codomain_sort;

  friend class BoolectorSolver;
};
}  // namespace smt

#endif
