#include <iostream>
#include <memory>

#include "assert.h"
#include "sort.h"

using namespace smt;
using namespace std;

constexpr bool kind2str_check()
{
  return ((kind2str[ARRAY] == "ARRAY") &&
          (kind2str[BOOL] == "BOOL") &&
          (kind2str[BV] == "BV") &&
          (kind2str[INT] == "INT") &&
          (kind2str[REAL] == "REAL") &&
          (kind2str[UNINTERPRETED] == "UNINTERPRETED"));
}

int main()
{
  static_assert(kind2str_check());
}
