#include <iostream>
#include <memory>
#include <vector>

#include "cvc5/cvc5.h"
#include "assert.h"
#include "cvc5_factory.h"
#include "smt.h"

using namespace std;
using namespace cvc5;

int main()
{
  Solver s;
  Sort boolsort = s.getBooleanSort();
  s.setOption("produce-interpolants", "true");
  s.setOption("incremental", "false");
  Term b1 = s.mkConst(boolsort, "b1");
  Term b2 = s.mkConst(boolsort, "b2");

  cout << (b2.getKind() == Kind::CONSTANT) << std::endl;

  if (b2.getKind() != Kind::CONSTANT)
  {
    throw std::exception();
  }

  s.assertFormula(s.mkTerm(Kind::AND, { b1, b2 }));
  Term I = s.getInterpolant(b2);

  if (!I.isNull())
  {
    cout << "got an interpolant: " << I << endl;
  }

  cout << (I == b2) << endl;

  if (I.getKind() != Kind::CONSTANT)
  {
    cout << "ERROR The interpolant should have kind CONSTANT but has kind: "
         << kindToString(I.getKind()) << endl;
  }

  return 0;
}
