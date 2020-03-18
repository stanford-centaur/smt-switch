#include "logging_sort.h"

using namespace std;

namespace smt {

// implementations
SortKind LoggingSort::get_sort_kind() const { return sk; }

bool LoggingSort::compare(const Sort s) const
{
  SortKind other_sk = s->get_sort_kind();
  if (sk != other_sk)
  {
    return false;
  }

  switch (sk)
  {
    case BOOL:
    case INT:
    case REAL: { return true;
    }
    case BV: { return get_width() == s->get_width();
    }
    case ARRAY:
    {
      return (get_indexsort() == s->get_indexsort())
             && (get_elemsort() == s->get_elemsort());
    }
    case FUNCTION:
    {
      SortVec domain_sorts = get_domain_sorts();
      SortVec other_domain_sorts = s->get_domain_sorts();
      Sort return_sort = get_codomain_sort();
      Sort other_return_sort = s->get_codomain_sort();

      if (domain_sorts.size() != other_domain_sorts.size()
          || return_sort != other_return_sort)
      {
        return false;
      }

      for (size_t i = 0; i < domain_sorts.size(); i++)
      {
        if (domain_sorts[i] != other_domain_sorts[i])
        {
          return false;
        }
      }

      return true;
    }
    case NUM_SORT_CONS:
    {
      // null sorts should not be equal
      return false;
    }
  }
}

size_t LoggingSort::hash() const { return sort->hash(); }

// BVLoggingSort

BVLoggingSort::BVLoggingSort(Sort s, uint64_t width)
    : super(BV, s), width(width)
{
}

BVLoggingSort::~BVLoggingSort() {}

uint64_t BVLoggingSort::get_width() const { return width; }

// ArrayLoggingSort

ArrayLoggingSort::ArrayLoggingSort(Sort s, Sort idxsort, Sort esort)
    : super(ARRAY, s), indexsort(idxsort), elemsort(esort)
{
}

ArrayLoggingSort::~ArrayLoggingSort() {}

Sort ArrayLoggingSort::get_indexsort() const { return indexsort; }

Sort ArrayLoggingSort::get_elemsort() const { return elemsort; }

// FunctionLoggingSort

FunctionLoggingSort::FunctionLoggingSort(Sort s, SortVec sorts, Sort rsort)
    : super(FUNCTION, s), domain_sorts(sorts), codomain_sort(rsort)
{
}

FunctionLoggingSort::~FunctionLoggingSort() {}

SortVec FunctionLoggingSort::get_domain_sorts() const
{
  return domain_sorts;
}

Sort FunctionLoggingSort::get_codomain_sort() const { return codomain_sort; }

// methods dispatched to underlying sort

}  // namespace smt
