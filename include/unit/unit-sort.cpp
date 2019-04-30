#include <iostream>
#include <memory>

#include "assert.h"
#include "sort.h"

using namespace smt;
using namespace std;

constexpr bool type2str_check()
{
  return ((type2str[ARRAY] == "Array") &&
          (type2str[BV] == "BV") &&
          (type2str[INT] == "INT") &&
          (type2str[REAL] == "REAL") &&
          (type2str[UNINTERPRETED] == "UNINTERPRETED"));
}

bool bv_sort_check()
{
  bool res = true;
  unsigned int width = 4;
  std::unique_ptr<Sort> bvsort(new BVSort(width));
  res &= (bvsort->get_width() == width);
  return res;
}

// bool array_sort_check()
// {
//   bool res = true;
//   unsigned int width = 4;
//   bvsort4 = BVSort(width);
//   ArraySort arrsort = ArraySort(bvsort4, bvsort4);
//   res &= (arrsort.)
// }

int main()
{
  static_assert(type2str_check());
  assert(bv_sort_check());
}
