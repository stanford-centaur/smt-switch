#ifndef SMT_CVC4_SORT_H
#define SMT_CVC4_SORT_H

#include <unordered_map>

#include "sort.h"

#include "api/cvc4cpp.h"
#include "api/cvc4cppkind.h"

namespace smt
{

  // forward declaration
  class CVC4Solver;

  class CVC4Sort : public AbsSort
  {
  public:
    CVC4Sort(::CVC4::api::Sort s) : sort(s) {};
    ~CVC4Sort() = default;
    std::string to_string() const override;
    unsigned int get_width() const override;
    Sort get_indexsort() const override;
    Sort get_elemsort() const override;
    std::vector<Sort> get_domain_sorts() const override;
    Sort get_codomain_sort() const override;
    bool compare(const Sort) const override;
    SortKind get_sort_kind() const override;

   protected:
    ::CVC4::api::Sort sort;

    friend class CVC4Solver;

  };

}

#endif
