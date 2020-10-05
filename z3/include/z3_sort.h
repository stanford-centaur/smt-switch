#include "sort.h"

#include "z3++.h"

namespace smt {

class Z3Sort : public AbsSort
	{
 public:
  //Z3Sort()
  //    {};
  Z3Sort(::z3::sort s) : sort(s) {};
  virtual ~Z3Sort(){};
  std::size_t hash() const override;
  unsigned int get_width() const override;
  Sort get_indexsort() const override;
  Sort get_elemsort() const override;
  std::vector<Sort> get_domain_sorts() const override;
  Sort get_codomain_sort() const override;
  bool compare(const Sort s) const override;
  SortKind get_sort_kind() const override;

 protected:
     ::z3::sort sort;

};
}
