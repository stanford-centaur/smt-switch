#include <iostream>

#include "sort.h"

#include "api/cvc4cpp.h"

#include "cvc4_term.h"

using namespace std;
using namespace CVC4::api;

using namespace smt;

int main()
{
  Solver slv;
  ::CVC4::api::Term x = slv.mkVar(slv.mkBitVectorSort(8), "x");
  ::CVC4::api::Sort cs = x.getSort();
  CVC4Term t(x);
  cout << t.get_sort() << endl;
  return 0;
}
