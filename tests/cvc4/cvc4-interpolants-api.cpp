#include <iostream>

#include "api/cvc4cpp.h"
#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "cvc4_factory.h"
#include "smt.h"

using namespace std;
using namespace CVC4::api;

int main()
{
  Solver s;
  Sort boolsort = s.getBooleanSort();
  s.setOption("produce-interpols", "conjecture");
  s.setOption("sygus-active-gen", "enum");
  s.setOption("incremental", "false");
  Term b1 = s.mkConst(boolsort, "b1");
  Term b2 = s.mkConst(boolsort, "b2");

  cout << (b2.getKind() == CONSTANT) << std::endl;

  if (b2.getKind() != CONSTANT)
  {
    throw std::exception();
  }

  s.assertFormula(s.mkTerm(AND, b1, b2));
  Term I;
  bool success = s.getInterpolant(b2, I);

  if (success)
  {
    cout << "got an interpolant: " << I << endl;
  }

  cout << (I == b2) << endl;

  if (I.getKind() != CONSTANT)
  {
    cout << "ERROR The interpolant should have kind CONSTANT but has kind: " << kindToString(I.getKind()) << endl;
  }

  return 0;
}

