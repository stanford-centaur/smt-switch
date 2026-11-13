/*!
 * \file bitwuzla_interpolator.cpp
 * \brief Bitwuzla implementation of AbsSmtInterpolator
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/bitwuzla_interpolator.h"

#include <bitwuzla/cpp/bitwuzla.h>

#include <cstddef>
#include <exception>
#include <fstream>
#include <iostream>
#include <memory>
#include <string>
#include <vector>

#include "smt-switch/bitwuzla_solver.h"
#include "smt-switch/bitwuzla_term.h"
#include "smt-switch/bitwuzla_term_manager.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/result.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/solver_utils.h"
#include "smt-switch/term.h"
#include "smt-switch/utils.h"

namespace smt {

BzlaInterpolator::BzlaInterpolator()
    : AbsSmtInterpolator(BZLA_INTERPOLATOR, std::make_shared<BzlaSolver>()),
      bzla_solver(std::static_pointer_cast<BzlaSolver>(backend_solver))
{
  initialize();
}

void BzlaInterpolator::initialize()
{
  bzla_solver->set_opt("produce-interpolants", "true");
}

void BzlaInterpolator::do_set_opt(const std::string & option,
                                  const std::string & value)
{
  if (option == "produce-interpolants")
  {
    throw IncorrectUsageException(
        "The Bitwuzla interpolator does not allow the option " + option);
  }
  if (option == "dump-queries")
  {
    // A special option for dumping interpolation queries to files.
    // The value is expected to contain a filename prefix.
    if (value.empty())
    {
      throw IncorrectUsageException(
          "The option dump-queries needs a non-empty value");
    }
    dump_queries_prefix = value;
    return;
  }
  bzla_solver->set_opt(option, value);
}

// delegate the interpolation procedure to `compute_seq_interpolants`
Result BzlaInterpolator::compute_interpolant(const Term & A,
                                             const Term & B,
                                             Term & out_I) const
{
  return interpolant_from_sequence(A, B, out_I);
}

Result BzlaInterpolator::compute_seq_interpolants(
    [[maybe_unused]] const TermVec & formulae,
    [[maybe_unused]] TermVec & out_I) const
{
#ifndef SMT_SWITCH_BITWUZLA_HAS_INTERPOLANTS
  throw NotImplementedException("Bitwuzla interpolates only from 0.9.0 on");
#else
  // refuse a formula from another term manager before changing any state
  std::vector<bitwuzla::Term> bformulae;
  bformulae.reserve(formulae.size());
  for (const Term & f : formulae)
  {
    bformulae.push_back(bzla_solver->bzla_term(f));
  }
  // count how many assertions can be reused; none when incremental is off,
  // so every formula the last query pushed is popped below
  size_t num_reused = 0;
  while (incremental_mode && num_reused < last_itp_query_assertions.size()
         && num_reused < formulae.size()
         && last_itp_query_assertions.at(num_reused) == formulae.at(num_reused))
  {
    ++num_reused;
  }

  // pop formulas that cannot be reused
  bzla_solver->get_bitwuzla()->pop(
      narrow_levels(last_itp_query_assertions.size() - num_reused));

  // update the interpolation groups and assertions
  last_itp_query_assertions.resize(num_reused);
  last_itp_query_assertions.reserve(formulae.size());

  // add new assertions from formulas
  for (size_t k = num_reused; k < formulae.size(); ++k)
  {
    // Add a new backtrack point and push the formula.
    bzla_solver->get_bitwuzla()->push(1);
    bzla_solver->get_bitwuzla()->assert_formula(bformulae.at(k));
    last_itp_query_assertions.push_back(formulae.at(k));
  }

  if (!dump_queries_prefix.empty())
  {
    // Note: the dumped query will only include the current assertions
    auto filename =
        dump_queries_prefix + "." + std::to_string(itp_query_count) + ".smt2";
    std::ofstream out(filename);
    if (!out)
    {
      std::cerr << "Warning: cannot open " << filename
                << " for writing, query not dumped" << std::endl;
    }
    else
    {
      bzla_solver->get_bitwuzla()->print_formula(out, "smt2");
      out.close();
      if (!out)
      {
        std::cerr << "Warning: cannot write " << filename
                  << ", query dump incomplete" << std::endl;
      }
    }
  }
  itp_query_count++;

  // solve query and get interpolants
  bitwuzla::Result bzla_res;
  try
  {
    bzla_res = bzla_solver->get_bitwuzla()->check_sat();
  }
  catch (std::exception & e)
  {
    throw SolverException(e.what());
  }

  if (bzla_res == bitwuzla::Result::SAT)
  {
    return Result(SAT);
  }
  else if (bzla_res == bitwuzla::Result::UNKNOWN)
  {
    return Result(UNKNOWN, "Interpolation failure");
  }

  Result r = Result(UNSAT);
  std::vector<std::vector<bitwuzla::Term>> partitions;
  for (size_t i = 0, n = formulae.size() - 1; i < n; ++i)
  {
    partitions.push_back({ bformulae.at(i) });
  }
  std::vector<bitwuzla::Term> itps;
  try
  {
    itps = bzla_solver->get_bitwuzla()->get_interpolants(partitions);
  }
  catch (const bitwuzla::Exception & e)
  {
    out_I.assign(partitions.size(), Term());
    return Result(UNKNOWN, std::string("Interpolation failure: ") + e.what());
  }
  // the interpolants belong to the term manager of the formulae
  const std::shared_ptr<BzlaTermManager> & formulae_tm =
      backend_pointer_cast<BzlaTerm>(formulae.at(0))->tm;
  for (const auto & itp : itps)
  {
    if (itp.is_null())
    {
      Term nullterm;
      out_I.push_back(nullterm);
      r = Result(UNKNOWN,
                 "Had at least one interpolation failure in "
                 "get_sequence_interpolants.");
    }
    else
    {
      out_I.push_back(std::make_shared<BzlaTerm>(itp, formulae_tm));
    }
  }

  return r;
#endif
}

// these terms belong to the term manager a reset destroys
void BzlaInterpolator::forget_queries() { last_itp_query_assertions.clear(); }

}  // namespace smt
