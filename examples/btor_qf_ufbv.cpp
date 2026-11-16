/*!
 * \file btor_qf_ufbv.cpp
 * \brief A small incremental QF_UFBV query solved with Boolector
 * \author Makai Mann
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <smt-switch/boolector_factory.h>
#include <smt-switch/smt.h>

#include <iostream>

int main()
{
  // Boolector aliases booleans and bitvectors of size one
  // and also performs on-the-fly rewriting
  // if you'd like to maintain the term structure, you can
  // enable logging by passing true
  smt::SmtSolver s = smt::BoolectorSolverFactory::create(false);

  s->set_logic("QF_UFBV");
  s->set_opt("incremental", "true");
  s->set_opt("produce-models", "true");
  s->set_opt("produce-unsat-assumptions", "true");
  smt::Sort bvs = s->make_sort(smt::BV, 32);
  smt::Sort funs = s->make_sort(smt::FUNCTION, { bvs, bvs });

  smt::Term x = s->make_symbol("x", bvs);
  smt::Term y = s->make_symbol("y", bvs);
  smt::Term f = s->make_symbol("f", funs);

  smt::Op ext = smt::Op(smt::Extract, 15, 0);
  smt::Term x0 = s->make_term(ext, x);
  smt::Term y0 = s->make_term(ext, y);

  smt::Term fx = s->make_term(smt::Apply, f, x);
  smt::Term fy = s->make_term(smt::Apply, f, y);
  s->assert_formula(s->make_term(smt::Distinct, fx, fy));

  s->push(1);
  s->assert_formula(s->make_term(smt::Equal, x0, y0));
  std::cout << s->check_sat() << std::endl;

  std::cout << s->get_value(x) << std::endl;
  s->pop(1);

  smt::Term xy = s->make_term(smt::BVAnd, x, y);
  smt::Term a1 = s->make_term(smt::BVUge, x0, y0);
  smt::Term a2 = s->make_term(smt::BVUge, xy, x);
  smt::Term a3 = s->make_term(smt::BVUge, xy, y);
  std::cout << s->check_sat_assuming({ a1, a2, a3 }) << std::endl;
  smt::UnorderedTermSet ua;
  s->get_unsat_assumptions(ua);
  for (smt::Term t : ua)
  {
    std::cout << t << std::endl;
  }
}
