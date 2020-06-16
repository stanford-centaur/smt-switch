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
#include <fstream>
#include <cstdio>
#include <stdexcept>
#include <string>
#include <array>
#include <iostream>
#include <memory>
#include <vector>
#include <sstream>
#include "assert.h"

// note: this file depends on the CMake build infrastructure
// specifically defined macros
// it cannot be compiled outside of the build
#include "test-utils.h"

#include "msat_factory.h"
#include "printing_solver.h"
#include "smt.h"

using namespace smt;
using namespace std;

/**
 * A function for running a process
 * Taken from: https://stackoverflow.com/questions/478898/how-do-i-execute-a-command-and-get-the-output-of-the-command-within-c-using-po
 */
std::string exec(const char* cmd) {
    std::array<char, 128> buffer;
    std::string result;
    std::unique_ptr<FILE, decltype(&pclose)> pipe(popen(cmd, "r"), pclose);
    if (!pipe) {
        throw std::runtime_error("popen() failed!");
    }
    while (fgets(buffer.data(), buffer.size(), pipe.get()) != nullptr) {
        result += buffer.data();
    }
    return result;
}

int main()
{
  stringbuf strbuf;
  SmtSolver msat = MsatSolverFactory::create_interpolating_solver();
  ostream os(&strbuf);
  SmtSolver s = create_printing_solver(msat, &os, PrintingStyleEnum::MSAT_STYLE);
  s->set_logic("QF_LIA");

  Sort intsort = s->make_sort(INT);

  Term x = s->make_symbol("x", intsort);
  Term y = s->make_symbol("y", intsort);
  Term z = s->make_symbol("z", intsort);

  Term A = s->make_term(And, s->make_term(Lt, x, y), s->make_term(Lt, y, z));
  Term B = s->make_term(Gt, x, z);
  Term I;
  bool got_interpolant = s->get_interpolant(A, B, I);

  string filename = "msat-printing.cpp-sample.smt2";
  std::ofstream out(filename.c_str());
  out << strbuf.str() << endl;
  out.close();
  // MSAT_HOME is a macro defined when built with MSAT
  // that points to the top-level MSAT directory
  // STRFY is defined in test-utils.h and converts
  // a macro to its string representation
  string command(STRFY(MSAT_HOME));
  command += "/bin/mathsat -interpolation=true ";
  command += filename;
  std::cout << "Running command: " << command << std::endl;
  string result = exec(command.c_str());
  std::cout << "got result:\n" << result << std::endl;
  assert(result == "unsat\n(<= 2 (+ z (* (- 1) x)))\n");
  remove(filename.c_str());
  return 0;
}
