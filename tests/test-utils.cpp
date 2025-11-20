/*********************                                                        */
/*! \file test-utils.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Convenience functions for testing.
**
**
**/

#include "test-utils.h"

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <array>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>

using namespace smt;

namespace smt_tests {

UnorderedTermSet get_free_symbols(Term & t)
{
  UnorderedTermSet free_symbols;
  TermVec to_visit({ t });
  UnorderedTermSet visited;

  Term n;
  while (to_visit.size())
  {
    n = to_visit.back();
    to_visit.pop_back();

    if (visited.find(n) == visited.end())
    {
      visited.insert(n);
      for (auto nn : n)
      {
        to_visit.push_back(nn);
      }

      if (n->is_symbolic_const())
      {
        free_symbols.insert(n);
      }
    }
  }

  return free_symbols;
}

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

void dump_and_run(SolverEnum solver,
                  std::stringbuf & strbuf,
                  std::vector<std::unordered_set<std::string>> expected_results,
                  std::string extra_opts)
{
  // Construct unique file name.
  std::string filename =
      testing::UnitTest::GetInstance()->current_test_case()->name();
  filename += "-sample.smt2";

  // Construct command string.
  std::string command;
  switch (solver)
  {
    // The paths to the binaries are defined by the build.
    case BZLA:
      command = STRFY(BITWUZLA_DIR);
      command += "/bin/bitwuzla ";
      break;
    case CVC5:
      command = STRFY(CVC5_HOME);
      command += "/build/bin/cvc5 ";
      break;
    default:
      throw std::runtime_error("unhandled solver: " + std::to_string(solver));
  }
  if (!extra_opts.empty())
  {
    command += extra_opts;
    command += " ";
  }
  command += filename;

  // Dump test case to file.
  std::ofstream out(filename.c_str());
  out << "; test case for " << command << std::endl;
  out << strbuf.str() << std::endl;
  out.close();

  // Run and check result.
  std::stringstream result(exec(command.c_str()));
  std::string line;
  std::size_t line_index = 0;
  while (std::getline(result, line))
  {
    auto expected_result = expected_results.at(line_index++);
    EXPECT_THAT(expected_result, testing::Contains(line));
  }
  EXPECT_EQ(line_index, expected_results.size());
  if (!testing::Test::HasFailure())
  {
    remove(filename.c_str());
  }
}

}  // namespace smt_tests
