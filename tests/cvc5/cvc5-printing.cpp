/*********************                                                        */
/*! \file cvc5-printinh.cpp
** \verbatim
** Top contributors (to current version):
**   Yoni Zohar
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief
**
**
**/
#include <array>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

#include "assert.h"

// note: this file depends on the CMake build infrastructure
// specifically defined macros
// it cannot be compiled outside of the build
#include "cvc5_factory.h"
#include "printing_solver.h"
#include "smt.h"
#include "test-utils.h"

using namespace smt;
using namespace std;

/**
 * A function for running a process
 * Taken from:
 * https://stackoverflow.com/questions/478898/how-do-i-execute-a-command-and-get-the-output-of-the-command-within-c-using-po
 */
std::string exec(const char * cmd)
{
  std::array<char, 128> buffer;
  std::string result;
  std::unique_ptr<FILE, decltype(&pclose)> pipe(popen(cmd, "r"), pclose);
  if (!pipe)
  {
    throw std::runtime_error("popen() failed!");
  }
  while (fgets(buffer.data(), buffer.size(), pipe.get()) != nullptr)
  {
    result += buffer.data();
  }
  return result;
}

void dump_and_run(stringbuf & strbuf,
                  string expected_result,
                  string extra_opts = "")
{
  string filename = "cvc5-printing.cpp-sample.smt2";
  std::ofstream out(filename.c_str());
  out << strbuf.str() << endl;
  out.close();
  // CVC5_HOME is a macro defined when built with cvc5
  // that points to the top-level cvc5 directory
  // STRFY is defined in test-utils.h and converts
  // a macro to its string representation
  string command(STRFY(CVC5_HOME));
  command += "/build/bin/cvc5 " + extra_opts + " ";
  command += filename;
  std::cout << "Running command: " << command << std::endl;
  string result = exec(command.c_str());
  std::cout << "got result:\n" << result << std::endl;
  assert(result == expected_result);
  remove(filename.c_str());
}

void test2(SmtSolver s, ostream & os, stringbuf & strbuf)
{
  s->set_logic("QF_LIA");
  Sort intsort = s->make_sort(INT);

  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term z = s->make_symbol("z", intsort);

  try
  {
    // x=0
    s->assert_formula(s->make_term(Equal, x, s->make_term(0, intsort)));
  }
  catch (IncorrectUsageException & e)
  {
    cout << e.what() << endl;
  }

  // x<y /\ y<z
  Term A = s->make_term(And, s->make_term(Lt, x, y), s->make_term(Lt, y, z));
  // x<z
  Term B = s->make_term(Gt, x, z);
  Term I;
  Result r = s->get_interpolant(A, B, I);
  dump_and_run(
      strbuf, "(define-fun I () Bool (<= x z))\n", "--produce-interpolants");
}

void test1(SmtSolver s, ostream & os, stringbuf & strbuf)
{
  s->set_logic("QF_AUFBV");
  s->set_opt("produce-models", "true");
  s->set_opt("incremental", "true");
  s->set_opt("produce-unsat-assumptions", "true");
  Sort us = s->make_sort("S", 0);
  Sort bvsort32 = s->make_sort(BV, 32);
  Sort fun_sort = s->make_sort(FUNCTION, SortVec{ bvsort32, us });
  Sort array32_32 = s->make_sort(ARRAY, bvsort32, bvsort32);
  Term x = s->make_symbol("x", bvsort32);
  Term y = s->make_symbol("y", bvsort32);
  Term arr = s->make_symbol("arr", array32_32);
  Term fun = s->make_symbol("f", fun_sort);

  Term S0 = s->make_symbol("s", us);

  Term ind1 = s->make_symbol("ind1", s->make_sort(BOOL));
  Term f = s->make_term(Equal, s->make_term(Apply, fun, x), S0);
  s->push(1);
  s->assert_formula(ind1);
  s->assert_formula(s->make_term(Equal, ind1, f));
  s->assert_formula(f);
  s->assert_formula(
      s->make_term(Not,
                   s->make_term(Implies,
                                s->make_term(Equal, x, y),
                                s->make_term(Equal,
                                             s->make_term(Select, arr, x),
                                             s->make_term(Select, arr, y)))));
  Result r = s->check_sat_assuming(TermVec{ ind1 });
  assert(r.is_unsat());
  UnorderedTermSet usc;
  s->get_unsat_assumptions(usc);
  s->pop(1);
  s->check_sat();
  s->get_value(x);
  dump_and_run(strbuf, "unsat\n(ind1)\nsat\n((x (_ bv0 32)))\n");
}

int main()
{
  stringbuf strbuf1;
  SmtSolver cvc5_1 = Cvc5SolverFactory::create(false);
  ostream os1(&strbuf1);
  SmtSolver s1 =
      create_printing_solver(cvc5_1, &os1, PrintingStyleEnum::DEFAULT_STYLE);
  s1->set_opt("bv-print-consts-as-indexed-symbols", "true");
  test1(s1, os1, strbuf1);

  stringbuf strbuf2;
  SmtSolver cvc5_2 = Cvc5SolverFactory::create_interpolating_solver();
  ostream os2(&strbuf2);
  SmtSolver s2 =
      create_printing_solver(cvc5_2, &os2, PrintingStyleEnum::CVC5_STYLE);
  s2->set_opt("bv-print-consts-as-indexed-symbols", "true");
  test2(s2, os2, strbuf2);

  return 0;
}
