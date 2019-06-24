#include <iostream>
#include <unordered_map>

#include "smt.h"

#include "api/cvc4cpp.h"

#include "cvc4_term.h"

using namespace std;

// using namespace smt;

int main()
{
  ::CVC4::api::Solver slv;
  ::CVC4::api::Term x = slv.mkVar(slv.mkBitVectorSort(8), "x");
  ::CVC4::api::Term y = slv.mkVar(slv.mkBitVectorSort(8), "y");
  ::smt::CVC4Term x1(x);
  // CVC4Term y1(y);
  ::smt::Term y1(new ::smt::CVC4Term(y));
  cout << y1->to_string() << endl;
  cout << y1->get_sort() << endl;
  // ::CVC4::api::Term cterm = slv.mkTerm(primop2kind.at(BVAdd), x, y);
  // Term t(new CVC4Term(cterm));
  // cout << t->to_string() << endl;
  // cout << t->get_sort() << endl;
  return 0;
}
