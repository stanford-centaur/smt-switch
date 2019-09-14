#include "solver.h"

#include "exceptions.h"

#include <iterator>
#include <sstream>

namespace smt {

// TODO: Implement a generic visitor

Term AbsSmtSolver::substitute(const Term term,
                              const UnorderedTermMap & substitution_map) const
{
  // cache starts with the substitutions
  UnorderedTermMap cache(substitution_map);
  TermVec to_visit{ term };
  TermVec cached_children;
  Term t;
  while (to_visit.size())
  {
    t = to_visit.back();
    to_visit.pop_back();
    if (cache.find(t) == cache.end())
    {
      // doesn't get updated yet, just marking as visited
      cache[t] = t;
      to_visit.push_back(t);
      for (auto c : t)
      {
        to_visit.push_back(c);
      }
    }
    else
    {
      cached_children.clear();
      for (auto c : t)
      {
        cached_children.push_back(cache.at(c));
      }

      if (cached_children.size())
      {
        cache[t] = make_term(t->get_op(), cached_children);
      }
    }
  }

  return cache.at(term);
}

Sort AbsSmtSolver::transfer_sort(const Sort sort)
{
  SortKind sk = sort->get_sort_kind();
  if ((sk == INT) || (sk == REAL))
  {
    return make_sort(sk);
  }
  else if (sk == BV)
  {
    return make_sort(sk, sort->get_width());
  }
  else if (sk == ARRAY)
  {
    // recursive call, but it should be okay because we don't expect deep nesting of arrays
    return make_sort(sk, transfer_sort(sort->get_indexsort()), transfer_sort(sort->get_elemsort()));
  }
  else if (sk == FUNCTION)
  {
    // recursive call, but it should be okay because we don't expect deep nesting of functions either
    std::vector<Sort> domain_sorts;
    for (auto s : sort->get_domain_sorts())
    {
      domain_sorts.push_back(transfer_sort(s));
    }
    return make_sort(sk, domain_sorts, transfer_sort(sort->get_codomain_sort()));
  }
  else
  {
    throw SmtException("Failed to transfer sort: " + sort->to_string());
  }
}

Term AbsSmtSolver::transfer_term(const Term term)
{
  UnorderedTermMap cache;
  TermVec to_visit { term };
  TermVec cached_children;
  Term t;
  Sort s;
  while (to_visit.size())
  {
    t = to_visit.back();
    to_visit.pop_back();

    if (cache.find(t) == cache.end())
    {
      // doesn't get updated yet, just marking as visited
      cache[t] = t;
      to_visit.push_back(t);
      for (auto c : t)
      {
        to_visit.push_back(c);
      }
    }
    else
    {
      cached_children.clear();
      for (auto c : t)
      {
        cached_children.push_back(cache.at(c));
      }

      if (cached_children.size())
      {
        cache[t] = make_term(t->get_op(), cached_children);
      }
      else if (t->is_symbolic_const())
      {
        s = transfer_sort(t->get_sort());
        std::string name = t->to_string();
        if (has_symbol(name))
        {
          // symbol cache hit
          cache[t] = lookup_symbol(name);
        }
        else
        {
          cache[t] = make_term(t->to_string(), s);
        }
      }
      else if (t->is_value())
      {
        s = transfer_sort(t->get_sort());
        cache[t] = value_from_smt2(t->to_string(), s);
      }
      else
      {
        throw SmtException("Can't transfer term: " + t->to_string());
      }
    }
  }

  return cache[term];
}

Term AbsSmtSolver::value_from_smt2(const std::string val, const Sort sort) const
{
  SortKind sk = sort->get_sort_kind();
  if (sk == BV)
  {
    // TODO: Only put checks in debug mode
    if (val.length() < 2)
    {
      throw IncorrectUsageException("Can't read " + val + " as a bit-vector sort.");
    }

    std::string prefix = val.substr(0, 2);
    std::string bvval;
    if (prefix == "(_")
    {
      std::istringstream iss(val);
      std::vector<std::string> tokens(std::istream_iterator<std::string>{iss},
                                      std::istream_iterator<std::string>());
      bvval = tokens[1];
      if (tokens[1].substr(0, 2) != "bv")
      {
        throw IncorrectUsageException("Can't read " + val + " as a bit-vector sort.");
      }

      bvval = bvval.substr(2, bvval.length()-2);
      return make_value(bvval, sort, 10);
    }
    else if (prefix == "#b")
    {
      bvval = val.substr(2, val.length()-2);
      return make_value(bvval, sort, 2);
    }
    else if (prefix == "#x")
    {
      bvval = val.substr(2, val.length()-2);
      return make_value(bvval, sort, 16);
    }
    else
    {
      throw IncorrectUsageException("Can't read " + val + " as a bit-vector sort.");
    }
  }
  else if ((sk == INT) || (sk == REAL))
  {
    return make_value(val, sort);
  }
  else
  {
    throw NotImplementedException("Only taking bv, int and real value terms currently.");
  }
}

}  // namespace smt
