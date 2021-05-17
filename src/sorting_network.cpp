/*********************                                                        */
/*! \file sorting_network.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Implements a symbolic sorting network for boolean-sorted variables.
**
**/

#include "sorting_network.h"

namespace smt {

// implementation based on SortingNetwork in the predecessor, CoSA:
// https://github.com/cristian-mattarei/CoSA/blob/141be4b23f4012c6ad5676907d7c211ae2b6614a/cosa/utils/formula_mngm.py#L198

TermVec SortingNetwork::sorting_network(const TermVec & unsorted) const
{
  if (unsorted.empty())
  {
    return {};
  }

  return sorting_network_rec(unsorted);
}

TermVec SortingNetwork::sorting_network_rec(const TermVec & unsorted) const
{
  size_t len = unsorted.size();
  if (len == 1)
  {
    return unsorted;
  }
  else if (len == 2)
  {
    return sort_two(unsorted[0], unsorted[1]);
  }

  size_t pivot = len / 2;
  auto begin = unsorted.begin();
  TermVec left_vec(begin, begin + pivot);
  TermVec right_vec(begin + pivot, unsorted.end());

  TermVec left_res = sorting_network_rec(left_vec);
  TermVec right_res = sorting_network_rec(right_vec);

  return merge(left_res, right_res);
}

TermVec SortingNetwork::sort_two(const Term & t1, const Term & t2) const
{
  return { solver_->make_term(Or, t1, t2), solver_->make_term(And, t1, t2) };
}

TermVec SortingNetwork::merge(const TermVec & sorted1,
                              const TermVec & sorted2) const
{
  size_t len1 = sorted1.size();
  size_t len2 = sorted2.size();

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

  for (size_t i = 0; i < len1; ++i)
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

  for (size_t i = 0; i < len2; ++i)
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
  size_t len_res_even = res_even.size();
  size_t len_res_odd = res_odd.size();

  TermVec res;
  res.reserve(len1 + len2);

  if (sorted1_is_even && sorted2_is_even)
  {
    Term first_res_odd = res_odd[0];
    res.push_back(first_res_odd);
    for (size_t i = 0; i < len_res_odd - 1; ++i)
    {
      const TermVec & two_sorted = sort_two(res_odd[i + 1], res_even[i]);
      assert(two_sorted.size() == 2);
      res.push_back(two_sorted[0]);
      res.push_back(two_sorted[1]);
    }

    Term last_res_even = res_even.back();
    res.push_back(last_res_even);
  }
  else if (sorted1_is_even && !sorted2_is_even)
  {
    Term first_res_odd = res_odd[0];
    res.push_back(first_res_odd);
    for (size_t i = 0; i < len_res_even; ++i)
    {
      const TermVec & two_sorted = sort_two(res_odd[i + 1], res_even[i]);
      assert(two_sorted.size() == 2);
      res.push_back(two_sorted[0]);
      res.push_back(two_sorted[1]);
    }
  }
  else if (!sorted1_is_even && !sorted2_is_even)
  {
    Term first_res_odd = res_odd[0];
    Term last_res_odd = res_odd.back();

    res.push_back(first_res_odd);
    for (size_t i = 0; i < len_res_even; ++i)
    {
      const TermVec & two_sorted = sort_two(res_odd[i + 1], res_even[i]);
      assert(two_sorted.size() == 2);
      res.push_back(two_sorted[0]);
      res.push_back(two_sorted[1]);
    }
    res.push_back(last_res_odd);
  }
  else
  {
    // should not occur to due normalization above
    assert(false);
  }

  assert(res.size() == len1 + len2);
  return res;
}

}  // namespace smt
