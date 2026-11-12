/*!
 * \file exec_utils.cpp
 * \brief Convenience functions for testing
 * \author Makai Mann
 * \author Áron Ricardo Perez-Lopez
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "exec_utils.h"

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <array>
#include <cstdio>
#include <fstream>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>

namespace smt_tests {

namespace {

// A stream from popen has to be closed with pclose, not fclose.
struct PipeCloser
{
  void operator()(FILE * f) const { pclose(f); }
};

}  // namespace

/**
 * A function for running a process
 * Taken from:
 * https://stackoverflow.com/questions/478898/how-do-i-execute-a-command-and-get-the-output-of-the-command-within-c-using-po
 */
std::string exec(const char * cmd)
{
  std::array<char, 128> buffer;
  std::string result;
  std::unique_ptr<FILE, PipeCloser> pipe(popen(cmd, "r"));
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

void dump_and_run(std::string_view executable_path,
                  std::stringbuf & strbuf,
                  std::vector<std::unordered_set<std::string>> expected_results,
                  std::string extra_opts)
{
  // Construct unique file name.
  std::string filename =
      testing::UnitTest::GetInstance()->current_test_case()->name();
  filename += "-sample.smt2";

  // Construct command string.
  std::string command(executable_path);
  command += " ";
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
