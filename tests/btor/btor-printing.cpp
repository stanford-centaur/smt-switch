/*********************                                                        */
/*! \file btor-printing.cpp
** \verbatim
** Top contributors (to current version):
**   Áron Ricardo Perez-Lopez
** This file is part of the smt-switch project.
** Copyright (c) 2025 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Test that PrintingSolver behaves correctly for Boolector.
**
** Note: this file depends on the CMake build infrastructure, specifically on
** defined macros. It cannot be compiled outside of the build.
**/
#include <cassert>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <string>

#include "gtest/gtest.h"

#include "boolector_factory.h"
#include "smt.h"
#include "printing_solver.h"
#include "test-utils.h"

using namespace smt;

TEST(BtorPrintingTest, SymbolName)
{
  std::string smt_filename = "btor-printing-test.smt2";
  std::ofstream smt_file(smt_filename, std::ios::trunc);
  SmtSolver solver = BoolectorSolverFactory::create(false);
  solver = create_printing_solver(solver, &smt_file, PrintingStyleEnum::DEFAULT_STYLE);
  solver->set_logic("QF_BV");
  solver->set_opt("incremental", "true");
  Sort sort = solver->make_sort(SortKind::BOOL);
  solver->push();
  Term term = solver->make_symbol("x", sort);
  solver->assert_formula(term);
  Result result = solver->check_sat();
  smt_file.close();
  EXPECT_TRUE(result.is_sat());

  std::string witness_filename = "btor-printing-test.witness";
  std::string command = STRFY(BTOR_HOME);
  command += "/build/bin/boolector ";
  command += smt_filename;
  command += " >";
  command += witness_filename;
  command += " 2>&1";
  std::system(command.c_str());
  std::remove(smt_filename.c_str());
  std::ifstream witness_file(witness_filename);
  std::stringstream output;
  witness_file >> output.rdbuf();
  witness_file.close();
  std::remove(witness_filename.c_str());
  std::string expected_output = "sat\n";
  EXPECT_EQ(output.str(), expected_output);
}
