#ifndef SMT_SORT_H
#define SMT_SORT_H

#include <string>
#include <unordered_set>
#include <vector>

#include "ops.h"
#include "smt_defs.h"

// Sort needs to have arguments
//  could be integers or other sorts
//  should use an enum for the different kinds of sorts probably

namespace smt {

  // TODO : add other smt kinds
enum SortKind
{
  ARRAY = 0,
  BOOL,
  BV,
  INT,
  REAL,
  FUNCTION,
  /** IMPORTANT: This must stay at the bottom.
      It's only use is for sizing the kind2str array
  */
  NUM_SORT_CONS
};

std::string to_string(SortKind);

/**
   Abstract base class for representing an SMT sort.
   It holds a kind enum and any necessary data for that particular sort.

   Sort objects should never be constructed directly, but instead provided
   by a Solver.
 */
class AbsSort
{
 public:
  AbsSort() {};
  virtual ~AbsSort(){};
  virtual std::string to_string() const;
  virtual std::size_t hash() const = 0;
  // TODO: decide on exception or special value for incorrect usage
  virtual uint64_t get_width() const = 0;
  virtual Sort get_indexsort() const = 0;
  virtual Sort get_elemsort() const = 0;
  virtual std::vector<Sort> get_domain_sorts() const = 0;
  virtual Sort get_codomain_sort() const = 0;
  virtual bool compare(const Sort sort) const = 0;
  virtual SortKind get_sort_kind() const = 0;
};

bool operator==(const Sort& s1, const Sort& s2);
bool operator!=(const Sort& s1, const Sort& s2);
std::ostream& operator<<(std::ostream& output, const Sort s);

// Useful typedefs for data structures
using SortVec = std::vector<Sort>;
using UnorderedSortSet = std::unordered_set<Sort>;

}  // namespace smt

namespace std
{

  template<>
  struct hash<smt::Sort>
  {
    size_t operator()(const smt::Sort & s) const
    {
      return s->hash();
    }
  };

}

#endif
