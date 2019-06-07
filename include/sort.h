#ifndef SMT_SORT_H
#define SMT_SORT_H

#include <memory>
#include <string>
#include <vector>

// Sort needs to have arguments
//  could be integers or other sorts
//  should use an enum for the different kinds of sorts probably

namespace smt {

// TODO : add other smt kinds
enum Kind
{
  ARRAY = 0,
  BOOL,
  BV,
  INT,
  REAL,
  UNINTERPRETED,
  /** IMPORTANT: This must stay at the bottom.
                 It's only use is for sizing the kind2str array
  */
  NUM_KINDS
};

std::string to_string(Kind k);

class AbsSort;
using Sort = std::shared_ptr<AbsSort>;

/**
   Abstract base class for representing an SMT sort.
   It holds a kind enum and any necessary data for that particular sort.

   Sort objects should never be constructed directly, but instead provided
   by a Solver.
 */
class AbsSort
{
 public:
  AbsSort(Kind k) : kind(k){};
  virtual ~AbsSort(){};
  std::string to_string() const;
  bool is_array() const { return kind == ARRAY; };
  bool is_bool() const { return kind == BOOL; };
  bool is_bv() const { return kind == BV; };
  bool is_int() const { return kind == INT; };
  bool is_real() const { return kind == REAL; };
  // TODO: decide on exception or special value for incorrect usage
  virtual unsigned int get_width() const = 0;
  virtual Sort get_indexsort() const = 0;
  virtual Sort get_elemsort() const = 0;
  virtual std::vector<Sort> get_domain_sorts() const = 0;
  virtual Sort get_codomain_sort() const = 0;
  virtual bool compare(const Sort absort) const = 0;
  Kind get_kind() const { return kind; };

 protected:
  Kind kind;
};

bool operator==(const Sort& s1, const Sort& s2);
std::ostream& operator<<(std::ostream& output, const Sort s);

}  // namespace smt

#endif
