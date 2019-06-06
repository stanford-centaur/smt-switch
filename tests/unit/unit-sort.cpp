#include <iostream>
#include <memory>

#include "assert.h"
#include "sort.h"

using namespace smt;
using namespace std;

bool kind2str_check()
{
  return ((to_string(ARRAY) == "ARRAY") && (to_string(BOOL) == "BOOL")
          && (to_string(BV) == "BV") && (to_string(INT) == "INT")
          && (to_string(REAL) == "REAL")
          && (to_string(UNINTERPRETED) == "UNINTERPRETED"));
}

int main()
{
  assert(kind2str_check());
  assert(to_string(ARRAY) == "ARRAY");
}
