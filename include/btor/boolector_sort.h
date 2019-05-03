#include <variant>

#include "exceptions.h"
#include "sort.h"

#include "boolector/boolector.h"

namespace smt
{
  class BoolectorSort : AbsSort
  {
  public:
    BoolectorSort(Kind k, Btor * b, BoolectorSort s) : AbsSort(k), btor(b), sort(s) {};
    virtual ~BoolectorSort() { boolector_release_sort(btor, sort); };
    // by default none of these work
    unsigned int get_width() const override { throw IncorrectUsageException("Only defined for a bit-vector sort."); };
    Sort get_indexsort() const override { throw IncorrectUsageException("Only defined for an array sort."); };
    Sort get_elemsort() const override  { throw IncorrectUsageException("Only defined for an array sort."); };
    std::vector<Sort> get_domain_sorts() const override  { throw IncorrectUsageException("Only defined for a function sort."); };
    Sort get_codomain_sort() const override  { throw IncorrectUsageException("Only defined for a function sort."); };
    bool compare(const Sort s) const override
    {
      std::shared_ptr<BoolectorSort> bs = std::static_pointer_cast<BoolectorSort>(s);
      if (kind != bs->get_kind())
      {
        // TODO : this will make bit-vectors and booleans different
        //        do we actually want this for boolector?
        return false;
      }

      switch(kind)
      {
      case ARRAY:
        return (get_indexsort() == bs->get_indexsort()) && (get_elemsort() == bs->get_elemsort());
        break;
      case BOOL:
      case BV:
        return width == bs->get_width();
        break;
      case UNINTERPRETED:
        std::vector<Sort> domain_sorts = get_domain_sorts();
        std::vector<Sort> bs_domain_sorts = bs->get_domain_sorts();

        if (domain_sorts.size() != bs_domain_sorts.size())
        {
          return false;
        }
        else if (get_codomain_sort() != bs->get_codomain_sort())
        {
          return false;
        }

        bool res = true;

        for (unsigned i=0; i < domain_sorts.size(); ++i)
        {
          res &= (domain_sorts[i] == bs_domain_sorts[i]);
        }

        return res;

      default:
        // unreachable -- thse are all the kinds that boolector supports
        assert(false);
      }
      return false;
    }
  protected:
    Kind kind;
    Btor * btor;
    BoolectorSort sort;
  };

  /** The Boolector C API doesn't support querying sorts for width, etc...
      (in Boolector asking for the width is done on a node, i.e. Term, rather than a sort)
      Thus, we need to track some extra information for implementing AbsSort.
      To make this simpler, we have unique classes for each sort.
   */

  class BoolectorBVSort : BoolectorSort
  {
  public:
    BoolectorBVSort(Kind k, Btor * b, BoolectorSort s, unsigned int w)
      : BoolectorSort(k, b, s), width(w) {};
    unsigned int get_width() const override { return width; };
  protected:
    unsigned width;
  };

  class BoolectorArraySort : BoolectorSort
  {
  public:
    BoolectorArraySort(Kind k, Btor * b, BoolectorSort s, Sort is, Sort es)
      : BoolectorSort(k, b, s), indexsort(is), elemsort(es) {};
    Sort get_indexsort() const override { return indexsort; };
    Sort get_elemsort()  const override { return elemsort; };
  protected:
    Sort indexsort;
    Sort elemsort;
  };

  class BoolectorFunctionSort : BoolectorSort
  {
  public:
    BoolectorFunctionSort(Kind k, Btor * b, BoolectorSort s, std::vector<Sort> sorts, Sort sort)
      : BoolectorSort(k, b, s), domain_sorts(sorts), codomain_sort(sort) {};
    std::vector<Sort> get_domain_sorts() const override { return domain_sorts; };
    Sort get_codomain_sort() const override { return codomain_sort; };
  protected:
    std::vector<Sort> domain_sorts;
    Sort codomain_sort;
  };
}
