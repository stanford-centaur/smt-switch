/*!
 * \file sorting_network.cpp
 * \brief Implements a symbolic sorting network for boolean-sorted variables
 * \author Makai Mann
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/sorting_network.h"

#include <cstddef>
#include <memory>
#include <string>
#include <vector>

#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

namespace smt {

// implementation based on SortingNetwork in the predecessor, CoSA:
// https://github.com/cristian-mattarei/CoSA/blob/141be4b23f4012c6ad5676907d7c211ae2b6614a/cosa/utils/formula_mngm.py#L198

SortingNetwork::SortingNetwork(const SmtSolver & solver) : solver_(solver) {}

TermVec SortingNetwork::sorting_network(const TermVec & unsorted) const
{
  if (unsorted.empty())
  {
    return {};
  }

  // check that all the terms in unsorted are boolean sorted
  // for sort aliasing solvers, best to compare to the object
  // rather than rely on the SortKind
  Sort boolsort = solver_->make_sort(BOOL);
  Sort sort;
  for (const auto & tt : unsorted)
  {
    sort = tt->get_sort();
    if (tt->get_sort() != boolsort)
    {
      throw IncorrectUsageException("Expected all boolean sorts but got "
                                    + tt->to_string() + ":"
                                    + sort->to_string());
    }
  }

  return sorting_network_rec(unsorted);
}

TermVec SortingNetwork::sort_two(const Term & t1, const Term & t2) const
{
  return { solver_->make_term(Or, t1, t2), solver_->make_term(And, t1, t2) };
}

TermVec SortingNetwork::merge(const TermVec & sorted1,
                              const TermVec & sorted2) const
{
  std::size_t len1 = sorted1.size();
  std::size_t len2 = sorted2.size();

  if (len1 == 0)
  {
    return sorted2;
  }
  else if (len2 == 0)
  {
    return sorted1;
  }
  else if (len1 == 1 && len2 == 1)
  {
    return sort_two(sorted1[0], sorted2[0]);
  }

  bool sorted1_is_even = (len1 % 2) == 0;
  bool sorted2_is_even = (len2 % 2) == 0;

  if (!sorted1_is_even and sorted2_is_even)
  {
    // normalize so we don't have to do all cases
    return merge(sorted2, sorted1);
  }

  TermVec even_sorted1;
  TermVec odd_sorted1;

  for (std::size_t i = 0; i < len1; ++i)
  {
    if (i % 2 == 0)
    {
      odd_sorted1.push_back(sorted1[i]);
    }
    else
    {
      even_sorted1.push_back(sorted1[i]);
    }
  }

  TermVec even_sorted2;
  TermVec odd_sorted2;

  for (std::size_t i = 0; i < len2; ++i)
  {
    if (i % 2 == 0)
    {
      odd_sorted2.push_back(sorted2[i]);
    }
    else
    {
      even_sorted2.push_back(sorted2[i]);
    }
  }

  TermVec res_even = merge(even_sorted1, even_sorted2);
  TermVec res_odd = merge(odd_sorted1, odd_sorted2);
  std::size_t len_res_even = res_even.size();
  std::size_t len_res_odd = res_odd.size();

  TermVec res;
  res.reserve(len1 + len2);

  if (sorted1_is_even && sorted2_is_even)
  {
    // if both inputs were even, they have same number of elements
    // need to interleave and compare all inner elements
    // the first odd result and last even result have already
    // been compared via the base case of merge (two length 1
    // lists)

    Term first_res_odd = res_odd[0];
    res.push_back(first_res_odd);
    for (std::size_t i = 0; i < len_res_odd - 1; ++i)
    {
      const TermVec & two_sorted = sort_two(res_odd[i + 1], res_even[i]);
      res.push_back(two_sorted[0]);
      res.push_back(two_sorted[1]);
    }

    Term last_res_even = res_even.back();
    res.push_back(last_res_even);
  }
  else if (sorted1_is_even && !sorted2_is_even)
  {
    // if first element was even and second was odd,
    //   then there's one extra element in the merged
    //   odd list
    // the first odd element has already been fully
    //   processed down to the base case of merge
    Term first_res_odd = res_odd[0];
    res.push_back(first_res_odd);
    for (std::size_t i = 0; i < len_res_even; ++i)
    {
      const TermVec & two_sorted = sort_two(res_odd[i + 1], res_even[i]);
      res.push_back(two_sorted[0]);
      res.push_back(two_sorted[1]);
    }
  }
  else
  {
    // if both inputs were odd, then there are
    // two more elements in the odd merged list
    // the first and last elements have already
    // been fully processed down to the base
    // case of merge
    // the rest need to be merged with the even
    // merged list
    Term first_res_odd = res_odd[0];
    Term last_res_odd = res_odd.back();

    res.push_back(first_res_odd);
    for (std::size_t i = 0; i < len_res_even; ++i)
    {
      const TermVec & two_sorted = sort_two(res_odd[i + 1], res_even[i]);
      res.push_back(two_sorted[0]);
      res.push_back(two_sorted[1]);
    }
    res.push_back(last_res_odd);
  }

  return res;
}

// protected methods

TermVec SortingNetwork::sorting_network_rec(const TermVec & unsorted) const
{
  std::size_t len = unsorted.size();
  if (len == 1)
  {
    return unsorted;
  }
  else if (len == 2)
  {
    return sort_two(unsorted[0], unsorted[1]);
  }

  std::size_t pivot = len / 2;
  auto begin = unsorted.begin();
  TermVec left_vec(begin, begin + pivot);
  TermVec right_vec(begin + pivot, unsorted.end());

  TermVec left_res = sorting_network_rec(left_vec);
  TermVec right_res = sorting_network_rec(right_vec);

  return merge(left_res, right_res);
}

}  // namespace smt
