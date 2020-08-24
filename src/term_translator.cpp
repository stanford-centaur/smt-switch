/*********************                                                        */
/*! \file term_translator.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Class for translating terms from one solver to another. Keeps
**        a cache so it can be called multiple times (without redeclaring
**        symbols, which would throw an exception).
**/

#include <iterator>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include "assert.h"

#include "sort_inference.h"
#include "utils.h"
#include "term_translator.h"

using namespace std;

namespace smt {

// boolean ops
const unordered_set<PrimOp> bool_ops({ And, Or, Xor, Not, Implies, Iff });

const unordered_set<PrimOp> bv_ops({
    Concat,      Extract,     BVNot,  BVNeg,       BVAnd,        BVOr,
    BVXor,       BVNand,      BVNor,  BVXnor,      BVAdd,        BVSub,
    BVMul,       BVUdiv,      BVSdiv, BVUrem,      BVSrem,       BVSmod,
    BVShl,       BVAshr,      BVLshr, BVComp,      BVUlt,        BVUle,
    BVUgt,       BVUge,       BVSlt,  BVSle,       BVSgt,        BVSge,
    Zero_Extend, Sign_Extend, Repeat, Rotate_Left, Rotate_Right, BV_To_Nat,
});

// boolean ops that can easily be represented with bit-vector operators
const unordered_map<PrimOp, PrimOp> bool_to_bv_ops({
    { And, BVAnd },
    { Or, BVOr },
    { Xor, BVXor },
    { Not, BVNot },
    { Equal, BVComp },
});

// bitvector ops that can easily be represented with boolean operators
const unordered_map<PrimOp, PrimOp> bv_to_bool_ops({ { BVAnd, And },
                                                     { BVOr, Or },
                                                     { BVXor, Xor },
                                                     { BVNot, Not },
                                                     { BVComp, Equal } });

Sort TermTranslator::transfer_sort(const Sort & sort) const
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
  // better to keep a separate set for visited
  // then if something is in the cache, we can
  // assume it's already been processed
  // not just visited
  UnorderedTermSet visited;
  TermVec cached_children;
  Term t;
  Sort s;
  while (to_visit.size())
  {
    t = to_visit.back();
    to_visit.pop_back();

    if (cache.find(t) != cache.end())
    {
      // cache hit
      // it's already been processed
      continue;
    }

    if (visited.find(t) == visited.end())
    {
      // doesn't get updated yet, just marking as visited
      visited.insert(t);
      // need to visit it again
      to_visit.push_back(t);
      for (auto c : t)
      {
        to_visit.push_back(c);
      }
    }
    else
    {
      if (t->is_symbol())
      {
        s = transfer_sort(t->get_sort());
        cache[t] = solver->make_symbol(t->to_string(), s);
      }
      else if (t->is_param())
      {
        s = transfer_sort(t->get_sort());
        cache[t] = solver->make_param(t->to_string(), s);
      }
      else if (t->is_value())
      {
        s = transfer_sort(t->get_sort());
        if (s->get_sort_kind() == ARRAY)
        {
          // special case for const-array
          assert(t->begin() != t->end());
          Term val = cache.at(*(t->begin()));
          Sort valsort = val->get_sort();
          if (s->get_sort_kind() != ARRAY)
          {
            throw SmtException("Expecting array sort but got: "
                               + s->to_string());
          }
          else if (s->get_elemsort() != valsort)
          {
            throw SmtException("Expecting element sort but got "
                               + val->get_sort()->to_string() + " and "
                               + s->to_string());
          }
          else if (valsort->get_sort_kind() == ARRAY)
          {
            throw NotImplementedException(
                "Transferring terms with multi-dimensional constant arrays is "
                "not yet supported. Please contact the developers.");
          }
          cache[t] = solver->make_term(val, s);
        }
        else
        {
          // pass the original sort here
          // allows us to transfer from a solver that doesn't alias sorts
          // to one that does alias sorts
          // the sort will be transferred again in value_from_smt2
          cache[t] = value_from_smt2(t->to_string(), t->get_sort());
        }
      }
      else
      {
        assert(!t->is_symbol());
        assert(!t->is_param());
        assert(!t->is_value());
        assert(!t->get_op().is_null());

        cached_children.clear();
        for (auto c : t)
        {
          cached_children.push_back(cache.at(c));
        }
        assert(cached_children.size());

        Op op = t->get_op();
        if (!check_sortedness(op, cached_children))
        {
          /* NOTE: interesting behavior here
             if transferring between two solvers that alias sorts
             e.g. two different instances of BTOR
             the sorted-ness check will still fail for something like
             Ite(BV{1}, BV{8}, BV{8})
             so we'll reach this point and cast
             but the cast won't actually do anything for BTOR
             in other words, check_sortedness is not guaranteed
             to hold after casting */
          cache[t] = cast_op(op, cached_children);
        }
        else
        {
          cache[t] = solver->make_term(t->get_op(), cached_children);
        }
      }
    }
  }

  assert(cache.find(term) != cache.end());
  // make sure the sort is as-expected and cast if not
  // for dealing with solvers that alias sorts

  return cache.at(term);
}

Term TermTranslator::transfer_term(const Term & term, const SortKind sk)
{
  Term transferred_term = transfer_term(term);
  Sort transferred_sort = transferred_term->get_sort();
  SortKind transferred_sk = transferred_sort->get_sort_kind();
  if (transferred_sk == sk)
  {
    return transferred_term;
  }

  // only handles Bool <-> BV1, and Int <-> Real
  // otherwise throws an exception

  // expect this to be the most common case
  if (transferred_sk == BV && transferred_sort->get_width() == 1 && sk == BOOL)
  {
    Sort sort = solver->make_sort(BOOL);
    return cast_term(transferred_term, sort);
  }
  else if (transferred_sk == BOOL && sk == BV)
  {
    Sort sort = solver->make_sort(BV, 1);
    return cast_term(transferred_term, sort);
  }
  else if (transferred_sk == INT && sk == REAL)
  {
    Sort sort = solver->make_sort(REAL);
    return cast_term(transferred_term, sort);
  }
  else if (transferred_sk == REAL && sk == INT)
  {
    Sort sort = solver->make_sort(INT);
    return cast_term(transferred_term, sort);
  }
  else
  {
    string msg("Cannot cast ");
    msg += transferred_term->to_string() + " to " + smt::to_string(sk);
    throw IncorrectUsageException(msg);
  }
}

std::string TermTranslator::infixize_rational(const std::string smtlib) const {
  // smtlib: (/ up down)
  // ind -- index
  std::string op;
  int ind_of_up_start = smtlib.find_first_of("/");
  if (ind_of_up_start == std::string::npos) {
    return smtlib;
  }
  ind_of_up_start += 2;
  op = "/";
    int ind_of_up_end = smtlib.find_first_of(' ', ind_of_up_start);
  assert(ind_of_up_end != std::string::npos);
  ind_of_up_end -= 1;
  int ind_of_down_start = ind_of_up_end + 2;
  int ind_of_down_end = smtlib.find_first_of(')', ind_of_down_start);
  assert(ind_of_down_end != std::string::npos);
  ind_of_down_end -= 1;
  std::string new_up = smtlib.substr(ind_of_up_start, ind_of_up_end - ind_of_up_start +1);
  std::string new_down = smtlib.substr(ind_of_down_start, ind_of_down_end - ind_of_down_start +1);
  std::string new_string = new_up + " " + op + " " + new_down;
  return new_string;
}

Term TermTranslator::value_from_smt2(const std::string val,
                                     const Sort orig_sort) const
{
  SortKind sk = orig_sort->get_sort_kind();
  Sort sort = transfer_sort(orig_sort);
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
    if (val.substr(0, 2) == "(-")
    {
      std::string posval = val.substr(3, val.length() - 4);
      posval = infixize_rational(posval);
      Term posterm = solver->make_term(posval, sort);
      return solver->make_term(Negate, posterm);
    }
    else
    {
      std::string mval = infixize_rational(val);
      return solver->make_term(mval, sort);
    }
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

Term TermTranslator::cast_op(Op op, const TermVec & terms) const
{
  assert(!check_sortedness(op, terms));
  PrimOp po = op.prim_op;

  // priority is turning bitvector operations to boolean operations
  // Heuristic, because boolector represents everything with bit-vector
  // operators, the most common scenario is turning bitvector ops to
  // boolean

  // case 1 -- bitvector to boolean op
  if (bv_to_bool_ops.find(po) != bv_to_bool_ops.end())
  {
    TermVec casted_children;
    casted_children.reserve(terms.size());
    Sort boolsort = solver->make_sort(BOOL);
    for (auto t : terms)
    {
      casted_children.push_back(cast_term(t, boolsort));
    }
    return solver->make_term(bv_to_bool_ops.at(po), casted_children);
  }
  // case 2 -- boolean to bitvector op
  else if (bool_to_bv_ops.find(po) != bool_to_bv_ops.end())
  {
    TermVec casted_children;
    casted_children.reserve(terms.size());
    Sort bv1sort = solver->make_sort(BV, 1);
    for (auto t : terms)
    {
      casted_children.push_back(cast_term(t, bv1sort));
    }
    return solver->make_term(bool_to_bv_ops.at(po), casted_children);
  }
  // case 3 -- cast all bit-vectors to booleans
  // a boolean operator that can't be converted to a bit-vector operator easily
  // (easily meaning by just switching the PrimOp)
  else if (bool_ops.find(po) != bool_ops.end())
  {
    TermVec casted_children;
    casted_children.reserve(terms.size());
    Sort boolsort = solver->make_sort(BOOL);
    for (auto t : terms)
    {
      casted_children.push_back(cast_term(t, boolsort));
    }
    return solver->make_term(po, casted_children);
  }
  // case 4 -- cast all booleans to bitvectors
  else if (bv_ops.find(po) != bv_ops.end())
  {
    TermVec casted_children;
    casted_children.reserve(terms.size());
    Sort bv1sort = solver->make_sort(BV, 1);
    for (auto t : terms)
    {
      if (t->get_sort()->get_sort_kind() == BOOL)
      {
        casted_children.push_back(cast_term(t, bv1sort));
      }
      else
      {
        // expecting a bit-vector
        assert(t->get_sort()->get_sort_kind() == BV);
        casted_children.push_back(t);
      }
    }
    return solver->make_term(op, casted_children);
  }
  // case 5 -- special case for Ite
  else if (po == Ite)
  {
    assert(terms.size() == 3);
    Sort boolsort = solver->make_sort(BOOL);
    Term cond = cast_term(terms[0], boolsort);

    Term ifbranch = terms[1];
    Term elsebranch = terms[2];

    if (ifbranch->get_sort() != elsebranch->get_sort())
    {
      // arbitrarily deciding to cast to the ifbranch sort
      elsebranch = cast_term(elsebranch, ifbranch->get_sort());
    }

    return solver->make_term(Ite, cond, ifbranch, elsebranch);
  }
  // case 7 -- special case for ARRAY select
  else if (po == Select)
  {
    // assuming the array itself doesn't need to be casted
    // only the index
    // we have no suport for or issue with that
    return solver->make_term(
        Select,
        terms[0],
        cast_term(terms[1], terms[0]->get_sort()->get_indexsort()));
  }
  // case 8 -- special case for ARRAY store
  else if (po == Store)
  {
    // assuming the array itself doesn't need to be casted
    // only the index
    // we have no suport for or issue with that
    Sort arrsort = terms[0]->get_sort();
    return solver->make_term(Store,
                             terms[0],
                             cast_term(terms[1], arrsort->get_indexsort()),
                             cast_term(terms[2], arrsort->get_elemsort()));
  }
  // case 9 -- special case for FUNCTION
  else if (po == Apply)
  {
    Sort funsort = terms[0]->get_sort();
    // assuming the function itself does not need to be cast
    TermVec casted_children;
    casted_children.reserve(terms.size());
    casted_children.push_back(terms[0]);
    SortVec domain_sorts = funsort->get_domain_sorts();
    assert(terms.size() + 1 == domain_sorts.size());
    for (size_t i = 1; i < terms.size(); ++i)
    {
      casted_children.push_back(cast_term(terms[i], domain_sorts[i - 1]));
    }
    return solver->make_term(Apply, casted_children);
  }
  // default case
  else
  {
    string msg("Cannot cast this operation: (");
    msg += op.to_string();
    for (auto t : terms)
    {
      msg += " " + t->to_string();
    }
    msg += ")";
    throw NotImplementedException(msg);
  }
}

Term TermTranslator::cast_term(const Term & term, const Sort & sort) const
{
  Sort cur_sort = term->get_sort();
  if (cur_sort == sort)
  {
    // nothing to do
    return term;
  }
  else if (term->is_value())
  {
    return cast_value(term, sort);
  }

  SortKind sk = sort->get_sort_kind();
  SortKind cur_sk = cur_sort->get_sort_kind();

  if (sk == BV && cur_sk == BOOL)
  {
    return solver->make_term(
        Ite, term, solver->make_term(1, sort), solver->make_term(0, sort));
  }
  else if (sk == BOOL && cur_sk == BV)
  {
    return solver->make_term(Equal, term, solver->make_term(1, cur_sort));
  }
  else if (sk == INT && cur_sk == REAL)
  {
    return solver->make_term(To_Int, term);
  }
  else if (sk == REAL && cur_sk == INT)
  {
    return solver->make_term(To_Real, term);
  }
  else
  {
    throw NotImplementedException("Cannot interpret " + term->to_string()
                                  + " as " + sort->to_string());
  }
}

Term TermTranslator::cast_value(const Term & term, const Sort & sort) const
{
  SortKind sk = sort->get_sort_kind();
  Sort cur_sort = term->get_sort();
  SortKind cur_sk = cur_sort->get_sort_kind();

  if (sk == BOOL && cur_sk == BV)
  {
    string term_repr = term->to_string();
    if (term_repr == "(_ bv1 1)" || term_repr == "#b1" || term_repr == "#x1")
    {
      return solver->make_term(true);
    }
    else if (term_repr == "(_ bv0 1)" || term_repr == "#b0"
             || term_repr == "#x0")
    {
      return solver->make_term(false);
    }
    else
    {
      throw SmtException("Cannot interpret " + term->to_string()
                         + " as a bool.");
    }
  }
  else if (sk == BV && cur_sk == BOOL)
  {
    if (sort->get_width() != 1)
    {
      throw SmtException("Cannot interpret " + term->to_string() + " as "
                         + sort->to_string());
    }

    string term_repr = term->to_string();
    if (term_repr == "true")
    {
      return solver->make_term(1, sort);
    }
    else if (term_repr == "false")
    {
      return solver->make_term(0, sort);
    }
    else
    {
      throw SmtException("Cannot interpret " + term->to_string() + " as "
                         + sort->to_string());
    }
  }
  else if (sk == ARRAY)
  {
    // this is a constant array
    // the only value that has SortKind ARRAY
    // make constant array by recursing on the element value
    return solver->make_term(cast_value(*(term->begin()), sort->get_elemsort()),
                             sort);
  }
  else
  {
    throw NotImplementedException("Interpreting " + term->to_string() + " as "
                                  + sort->to_string()
                                  + " is not yet implemented.");
  }
}

}  // namespace smt
