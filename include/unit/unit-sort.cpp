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

int main()
{
  static_assert(type2str_check());
}
