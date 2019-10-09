#ifndef SMT_MSAT_SORT_H
#define SMT_MSAT_SORT_H

#include "sort.h"

#include "mathsat.h"

namespace smt {
// forward declaration
class MsatSolver;

// TODO
// THOUGHTS
// to implement UF, might need to optionally store a msat_decl
// because all the function things are defined on the decl itself
// could always just create a dummy one

class MsatSort : public AbsSort
{
 public:
  MsatSort(msat_env e, msat_type t) : env(e), type(t){};
  ~MsatSort() = default;
  std::string to_string() const override;
  std::size_t hash() const override;
  unsigned int get_width() const override;
  Sort get_indexsort() const override;
  Sort get_elemsort() const override;
  std::vector<Sort> get_domain_sorts() const override;
  Sort get_codomain_sort() const override;
  bool compare(const Sort) const override;
  SortKind get_sort_kind() const override;

 protected:
  msat_env env;
  msat_type type;

  friend class MsatSolver;
};

}  // namespace smt

#endif
