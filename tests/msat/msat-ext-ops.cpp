#include <iostream>
#include <memory>
#include <vector>
#include "assert.h"

#include "msat_factory.h"
#include "smt.h"
// after a full installation
// #include "smt-switch/msat_factory.h"
// #include "smt-switch/smt.h"

using namespace smt;
using namespace std;

// Tests for ops that MathSAT doesn't support directly
// We had to rewrite them using other primitive ops

int main()
{
  SmtSolver s = MsatSolverFactory::create();
  s->set_opt("produce-models", "true");
  s->set_opt("incremental", "true");

  Sort boolsort = s->make_sort(BOOL);
  Term a = s->make_term("a", boolsort);
  Term b = s->make_term("b", boolsort);

  // xor
  Result r = s->check_sat_assuming({s->make_term(Distinct,
                                                 s->make_term(Xor, a, b),
                                                 s->make_term(Or,
                                                              s->make_term(And, a, s->make_term(Not, b)),
                                                              s->make_term(And, s->make_term(Not, a), b)))});
  assert(r.is_unsat());

  // implies
  r = s->check_sat_assuming({s->make_term(Distinct,
                                          s->make_term(Implies, a, b),
                                          s->make_term(Not,
                                                       s->make_term(And,
                                                                    a,
                                                                    s->make_term(Not, b))))});
  assert(r.is_unsat());

  // distinct
  r = s->check_sat_assuming({s->make_term(Not,
                                          s->make_term(Equal,
                                                       s->make_term(Distinct, a, b),
                                                       s->make_term(Not,
                                                                    s->make_term(Equal,
                                                                                 a, b))))});
  assert(r.is_unsat());

  r = s->check_sat();
  assert(r.is_sat());

  Sort bvsort8 = s->make_sort(BV, 8);
  Term x = s->make_term("x", bvsort8);
  Term y = s->make_term("y", bvsort8);

  // BVNand
  r = s->check_sat_assuming({s->make_term(Distinct,
                                          s->make_term(BVNand, x, y),
                                          s->make_term(BVNot,
                                                       s->make_term(BVAnd, x, y)))});
  assert(r.is_unsat());

  // BVNor
  r = s->check_sat_assuming({s->make_term(Distinct,
                                          s->make_term(BVNor, x, y),
                                          s->make_term(BVNot,
                                                       s->make_term(BVOr, x, y)))});
  assert(r.is_unsat());

  // BVXnor
  r = s->check_sat_assuming({s->make_term(Distinct,
                                          s->make_term(BVXnor, x, y),
                                          s->make_term(BVNot,
                                                       s->make_term(BVXor, x, y)))});
  assert(r.is_unsat());

  // BVSmod
  size_t width = x->get_sort()->get_width();

  Term zero_1bit = s->make_value(0, s->make_sort(BV, 1));
  Term one_1bit = s->make_value(1, s->make_sort(BV, 1));
  Term zero_width = s->make_value(0, s->make_sort(BV, width));

  Term msb_x = s->make_term(Op(Extract, width - 1, width - 1), x);
  Term msb_y = s->make_term(Op(Extract, width - 1, width - 1), y);

  Term abs_x = s->make_term(
      Ite, s->make_term(Equal, msb_x, zero_1bit), x, s->make_term(BVNeg, x));
  Term abs_y = s->make_term(
      Ite, s->make_term(Equal, msb_y, zero_1bit), y, s->make_term(BVNeg, y));

  Term u = s->make_term(BVUrem, abs_x, abs_y);

  Term smod_def = s->make_term(
      Ite,
      s->make_term(Equal, u, zero_width),
      u,
      s->make_term(
          Ite,
          s->make_term(And,
                       s->make_term(Equal, msb_x, zero_1bit),
                       s->make_term(Equal, msb_y, zero_1bit)),
          u,
          s->make_term(
              Ite,
              s->make_term(And,
                           s->make_term(Equal, msb_x, one_1bit),
                           s->make_term(Equal, msb_y, zero_1bit)),
              s->make_term(BVAdd, s->make_term(BVNeg, u), y),
              s->make_term(Ite,
                           s->make_term(And,
                                        s->make_term(Equal, msb_x, zero_1bit),
                                        s->make_term(Equal, msb_y, one_1bit)),
                           s->make_term(BVAdd, u, y),
                           s->make_term(BVNeg, u)))));

  r = s->check_sat_assuming(
      { s->make_term(Distinct, s->make_term(BVSmod, x, y), smod_def) });
  assert(r.is_unsat());

  // BVUgt
  r = s->check_sat_assuming({s->make_term(Not,
                                          s->make_term(Or,
                                                       s->make_term(BVUle, x, y),
                                                       s->make_term(BVUgt, x, y)))});
  assert(r.is_unsat());

  // BVUge
  r = s->check_sat_assuming({s->make_term(Not,
                                          s->make_term(Or,
                                                       s->make_term(BVUlt, x, y),
                                                       s->make_term(BVUge, x, y)))});
  assert(r.is_unsat());

  // BVSgt
  r = s->check_sat_assuming({s->make_term(Not,
                                          s->make_term(Or,
                                                       s->make_term(BVSle, x, y),
                                                       s->make_term(BVSgt, x, y)))});
  assert(r.is_unsat());

  // BVSge
  r = s->check_sat_assuming({s->make_term(Not,
                                          s->make_term(Or,
                                                       s->make_term(BVSlt, x, y),
                                                       s->make_term(BVSge, x, y)))});
  assert(r.is_unsat());

  // Integer tests
  r = s->check_sat();
  assert(r.is_sat());

  Sort intsort = s->make_sort(INT);
  Term w = s->make_term("w", intsort);
  Term v = s->make_term("v", intsort);
  Term zero = s->make_value(0, intsort);

  // Negate
  r = s->check_sat_assuming({s->make_term(Distinct,
                                          s->make_term(Plus,
                                                       w,
                                                       s->make_term(Negate, w)),
                                          zero)});
  assert(r.is_unsat());

  // Abs
  r = s->check_sat_assuming({s->make_term(Not, s->make_term(Ge,
                                                            s->make_term(Abs,
                                                                         v),
                                                            zero))});
  assert(r.is_unsat());

  // Is_Int
  Term onep3 = s->make_term("onep3", s->make_sort(REAL));
  r = s->check_sat_assuming({s->make_term(Equal, onep3, s->make_value("1.3", s->make_sort(REAL))),
                             s->make_term(Is_Int, onep3)});
  assert(r.is_unsat());

  // Minus
  r = s->check_sat_assuming({s->make_term(Distinct,
                                         s->make_term(Minus, v, v),
                                         zero)});
  assert(r.is_unsat());

  // Lt
  r = s->check_sat_assuming({s->make_term(Not,
                                          s->make_term(Or,
                                                       s->make_term(Lt, w, v),
                                                       s->make_term(Ge, w, v)))});
  assert(r.is_unsat());

  // Gt
  r = s->check_sat_assuming({s->make_term(Not,
                                          s->make_term(Or,
                                                       s->make_term(Gt, w, v),
                                                       s->make_term(Le, w, v)))});
  assert(r.is_unsat());

  // Ge
  r = s->check_sat_assuming({s->make_term(Not,
                                          s->make_term(Or,
                                                       s->make_term(Ge, w, v),
                                                       s->make_term(Lt, w, v)))});
  assert(r.is_unsat());

  return 0;
}
