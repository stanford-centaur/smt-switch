#include <iostream>

#include "assert.h"
#include "smt.h"
#include "z3_factory.h"
#include "z3_sort.h"

using namespace smt;
using namespace std;
// using namespace z3;

int main()
{
  SmtSolver s = Z3SolverFactory::create(false);

  cout << ":)" << endl;

  Sort intsort = s->make_sort(INT);
  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term val1 = s->make_term(1, intsort);
  Term val3 = s->make_term(3, intsort);

  cout << x << endl << y << endl << val1 << endl << val3 << endl;

  Term xge = s->make_term(Op(Ge), x, val1);
  Term xplus = s->make_term(Op(Plus), x, val3);
  Term ylt = s->make_term(Op(Lt), y, xplus);

  cout << xge << endl << xplus << endl << ylt << endl;

  s->assert_formula(xge);
  s->assert_formula(ylt);

  Result r = s->check_sat();
  cout << r << endl;


  Term xlt = s->make_term(Op(Lt), x, val1);
  s->assert_formula(xlt);
  r = s->check_sat();
  cout << r << endl;

  Sort bvsort = s->make_sort(BV, 7);
  cout << "bv val " << s->make_term("0000010", bvsort, 2) << endl;
  cout << "bv val " << s->make_term("0F", bvsort, 16) << endl;

  return 0;
}
