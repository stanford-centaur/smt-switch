/*********************                                                        */
/*! \file msat-printing.cpp
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
#include <cassert>
#include <cstddef>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

#include "msat_factory.h"
#include "printing_solver.h"
#include "smt.h"
#include "test-utils.h"

using namespace smt;

/**
 * A function for running a process
 * Taken from:
 * https://stackoverflow.com/questions/478898/how-do-i-execute-a-command-and-get-the-output-of-the-command-within-c-using-po
 */
std::string exec(const char * cmd)
{
  std::array<char, 128> buffer;
  std::string result;
  std::unique_ptr<FILE> pipe(popen(cmd, "r"));
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

int main()
{
  std::stringbuf strbuf;
  SmtSolver msat = MsatSolverFactory::create_interpolating_solver();
  std::ostream os(&strbuf);
  SmtSolver s =
      create_printing_solver(msat, &os, PrintingStyleEnum::MSAT_STYLE);
  s->set_logic("QF_LIA");

  Sort intsort = s->make_sort(INT);

  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term z = s->make_symbol("z", intsort);

  Term A = s->make_term(And, s->make_term(Lt, x, y), s->make_term(Lt, y, z));
  Term B = s->make_term(Gt, x, z);
  Term I;
  Result r = s->get_interpolant(A, B, I);
  assert(r.is_unsat());

  Term A1 = s->make_term(And, s->make_term(Lt, z, y), s->make_term(Lt, y, x));
  Term B1 = s->make_term(Gt, z, x);
  Term I1;
  Result r1 = s->get_interpolant(A1, B1, I1);
  assert(r1.is_unsat());

  std::string filename = "msat-printing.cpp-sample.smt2";
  std::ofstream out(filename.c_str());
  out << strbuf.str() << std::endl;
  out.close();
  // MSAT_HOME is a macro defined when built with MSAT
  // that points to the top-level MSAT directory
  // STRFY is defined in test-utils.h and converts
  // a macro to its string representation
  std::string command(STRFY(MSAT_HOME));
  command += "/bin/mathsat -interpolation=true ";
  command += filename;
  std::cout << "Running command: " << command << std::endl;
  std::string result = exec(command.c_str());
  std::cout << "got result:\n" << result << std::endl;

  const std::string unsat_result = "unsat";
  const std::vector<std::unordered_set<std::string>> interp_results = {
    { "(<= 2 (+ z (* (- 1) x)))", "(<= (+ x (* (- 1) z)) (- 2))" },
    { "(<= 2 (+ x (* (- 1) z)))", "(<= (+ z (* (- 1) x)) (- 2))" }
  };
  bool expect_interp = false;
  std::size_t interp_index = 0;
  for (std::string::size_type pos = 0;; pos = result.find("\n", pos) + 1)
  {
    if (interp_index == interp_results.size())
    {
      break;
    }
    else if (expect_interp)
    {
      bool interp_result_found = false;
      for (const auto & interp_result : interp_results.at(interp_index++))
      {
        if (result.substr(pos, interp_result.length()) == interp_result)
        {
          interp_result_found = true;
          break;
        }
      }
      assert(interp_result_found);
    }
    else
    {
      assert(result.substr(pos, unsat_result.size()) == unsat_result);
    }
    expect_interp = !expect_interp;
  }

  remove(filename.c_str());
  return 0;
}
