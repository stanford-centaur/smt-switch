#include <iterator>
#include <sstream>

#include "term_translator.h"

namespace smt {

Sort TermTranslator::transfer_sort(const Sort & sort)
{
  SortKind sk = sort->get_sort_kind();
  if ((sk == INT) || (sk == REAL) || (sk == BOOL))
  {
    return solver->make_sort(sk);
  }
  else if (sk == BV)
  {
    return solver->make_sort(sk, sort->get_width());
  }
  else if (sk == ARRAY)
  {
    // recursive call, but it should be okay because we don't expect deep
    // nesting of arrays
    return solver->make_sort(sk,
                             transfer_sort(sort->get_indexsort()),
                             transfer_sort(sort->get_elemsort()));
  }
  else if (sk == FUNCTION)
  {
    // recursive call, but it should be okay because we don't expect deep
    // nesting of functions either
    SortVec sorts;
    for (auto s : sort->get_domain_sorts())
    {
      sorts.push_back(transfer_sort(s));
    }
    sorts.push_back(transfer_sort(sort->get_codomain_sort()));
    return solver->make_sort(sk, sorts);
  }
  else
  {
    throw SmtException("Failed to transfer sort: " + sort->to_string());
  }
}

Term TermTranslator::transfer_term(const Term & term)
{
  if (cache.find(term) != cache.end())
  {
    return cache.at(term);
  }

  TermVec to_visit{ term };
  TermVec cached_children;
  Term t;
  Sort s;
  while (to_visit.size())
  {
    t = to_visit.back();
    to_visit.pop_back();

    if (cache.find(t) == cache.end())
    {
      if (t->is_symbolic_const())
      {
        s = transfer_sort(t->get_sort());
        std::string name = t->to_string();
        cache[t] = solver->make_symbol(t->to_string(), s);
      }
      else
      {
        // doesn't get updated yet, just marking as visited
        cache[t] = t;
        // need to visit it again
        to_visit.push_back(t);
        for (auto c : t)
        {
          to_visit.push_back(c);
        }
      }
    }
    else
    {
      cached_children.clear();
      for (auto c : t)
      {
        cached_children.push_back(cache.at(c));
      }

      if (t->is_value())
      {
        s = transfer_sort(t->get_sort());
        if (s->get_sort_kind() == ARRAY)
        {
          // special case for const-array
          Term val = cache.at(*(t->begin()));
          if (s->get_sort_kind() != ARRAY)
          {
            throw SmtException("Expecting array sort but got: "
                               + s->to_string());
          }
          else if (s->get_elemsort() != val->get_sort())
          {
            throw SmtException("Expecting element sort but got "
                               + val->get_sort()->to_string() + " and "
                               + s->to_string());
          }
          cache[t] = solver->make_term(val, s);
        }
        else
        {
          cache[t] = value_from_smt2(t->to_string(), s);
        }
      }
      else if (cached_children.size())
      {
        cache[t] = solver->make_term(t->get_op(), cached_children);
      }
      else if (t->is_symbolic_const())
      {
        // already created symbol and added to cache
        continue;
      }
      else
      {
        throw SmtException("Can't transfer term: " + t->to_string());
      }
    }
  }

  return cache[term];
}

Term TermTranslator::value_from_smt2(const std::string val,
                                     const Sort sort) const
{
  SortKind sk = sort->get_sort_kind();
  if (sk == BV)
  {
    // TODO: Only put checks in debug mode
    if (val.length() < 2)
    {
      throw IncorrectUsageException("Can't read " + val
                                    + " as a bit-vector sort.");
    }

    std::string prefix = val.substr(0, 2);
    std::string bvval;
    if (prefix == "(_")
    {
      std::istringstream iss(val);
      std::vector<std::string> tokens(std::istream_iterator<std::string>{ iss },
                                      std::istream_iterator<std::string>());
      bvval = tokens[1];
      if (tokens[1].substr(0, 2) != "bv")
      {
        throw IncorrectUsageException("Can't read " + val
                                      + " as a bit-vector sort.");
      }

      bvval = bvval.substr(2, bvval.length() - 2);
      return solver->make_term(bvval, sort, 10);
    }
    else if (prefix == "#b")
    {
      bvval = val.substr(2, val.length() - 2);
      return solver->make_term(bvval, sort, 2);
    }
    else if (prefix == "#x")
    {
      bvval = val.substr(2, val.length() - 2);
      return solver->make_term(bvval, sort, 16);
    }
    else
    {
      throw IncorrectUsageException("Can't read " + val
                                    + " as a bit-vector sort.");
    }
  }
  else if ((sk == INT) || (sk == REAL))
  {
    return solver->make_term(val, sort);
  }
  // this check HAS to come after bit-vector check
  // because boolector aliases those two sorts
  else if (sk == BOOL)
  {
    if (val != "true" && val != "false")
    {
      throw SmtException("Unexpected boolean value: " + val);
    }
    else
    {
      return solver->make_term(val == "true");
    }
  }
  else
  {
    throw NotImplementedException(
        "Only taking bool, bv, int and real value terms currently.");
  }
}

}  // namespace smt
