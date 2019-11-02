#ifndef SMT_MSAT_SORT_H
#define SMT_MSAT_SORT_H

#include "sort.h"

#include "mathsat.h"

namespace smt {
// forward declaration
class MsatSolver;

class MsatSort : public AbsSort
{
 public:
  MsatSort(msat_env e, msat_type t) : env(e), type(t), is_uf_type(false) {};
  MsatSort(msat_env e, msat_type t, msat_decl d) : env(e), type(t), uf_decl(d), is_uf_type(true) {};
  ~MsatSort() = default;
  std::size_t hash() const override;
  unsigned int get_width() const override;
  Sort get_indexsort() const override;
  Sort get_elemsort() const override;
  SortVec get_domain_sorts() const override;
  Sort get_codomain_sort() const override;
  bool compare(const Sort) const override;
  SortKind get_sort_kind() const override;

 protected:
  msat_env env;
  msat_type type;
  msat_decl uf_decl;
  bool is_uf_type;

  friend class MsatSolver;
};

}  // namespace smt

#endif
