#include <iostream>
#include <vector>

#include "cvc5/cvc5.h"

using namespace std;
using namespace cvc5;

int main()
{
  TermManager tm;
  Sort boolsort = tm.getBooleanSort();
  Term b1 = tm.mkConst(boolsort, "b1");
  Term b2 = tm.mkConst(boolsort, "b2");

  cout << (b2.getKind() == Kind::CONSTANT) << std::endl;

  if (b2.getKind() != Kind::CONSTANT)
  {
    throw std::exception();
  }

  Solver s(tm);
  s.setOption("produce-interpolants", "true");
  s.setOption("incremental", "false");
  s.assertFormula(tm.mkTerm(Kind::AND, { b1, b2 }));
  Term I = s.getInterpolant(b2);

  if (!I.isNull())
  {
    cout << "got an interpolant: " << I << endl;
  }

  cout << (I == b2) << endl;

  if (I.getKind() != Kind::CONSTANT)
  {
    cout << "ERROR The interpolant should have kind CONSTANT but has kind: "
         << to_string(I.getKind()) << endl;
  }

  return 0;
}
