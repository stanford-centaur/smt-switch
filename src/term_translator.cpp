/*!
 * \file term_translator.cpp
 * \brief Class for translating terms from one solver to another
 * \author Makai Mann
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * It keeps a cache, so it can be called several times without redeclaring
 * symbols, which would throw an exception.
 */
#include "smt-switch/term_translator.h"

#include <algorithm>
#include <cstdint>
#include <iterator>
#include <memory>
#include <sstream>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "smt-switch/datatype.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"
#include "smt-switch/term_builder.h"

namespace smt {

namespace {

// Whether a sort is or contains an uninterpreted sort
bool uses_uninterp_sort(const Sort & sort)
{
  bool res = false;
  SortKind sk = sort->get_kind();
  if (sk == SortKind::UNINTERPRETED)
  {
    res = true;
  }
  else if (sk == SortKind::FUNCTION)
  {
    for (auto s : sort->get_domain_sorts())
    {
      res |= uses_uninterp_sort(s);
    }
    res |= uses_uninterp_sort(sort->get_codomain_sort());
  }
  else if (sk == SortKind::ARRAY)
  {
    res |= uses_uninterp_sort(sort->get_indexsort());
    res |= uses_uninterp_sort(sort->get_elemsort());
  }

  return res;
}

}  // namespace

TermTranslator::TermTranslator(const TermBuilder & s) : term_builder(s)
{
  auto solver = std::dynamic_pointer_cast<AbsSmtSolver>(s);
  if (solver && solver->get_kind() == solvers::GENERIC)
  {
    throw NotImplementedException(
        "Generic Solvers do not support term transfer");
  }
}

Sort TermTranslator::transfer_sort(const Sort & sort)
{
  SortKind sk = sort->get_kind();
  if ((sk == SortKind::INT) || (sk == SortKind::REAL) || (sk == SortKind::BOOL)
      || (sk == SortKind::STRING))
  {
    return term_builder->make_sort(sk);
  }
  else if (sk == SortKind::BV)
  {
    return term_builder->make_sort(sk, sort->get_width());
  }
  else if (sk == SortKind::ARRAY)
  {
    // recursive call, but it should be okay because we don't expect deep
    // nesting of arrays
    return term_builder->make_sort(sk,
                                   transfer_sort(sort->get_indexsort()),
                                   transfer_sort(sort->get_elemsort()));
  }
  else if (sk == SortKind::FUNCTION)
  {
    // recursive call, but it should be okay because we don't expect deep
    // nesting of functions either
    SortVec sorts;
    for (auto s : sort->get_domain_sorts())
    {
      sorts.push_back(transfer_sort(s));
    }
    sorts.push_back(transfer_sort(sort->get_codomain_sort()));
    return term_builder->make_sort(sk, sorts);
  }
  else if (sk == SortKind::UNINTERPRETED)
  {
    // an applied sort constructor has parameters, a declared sort has none
    SortVec param_sorts = sort->get_uninterpreted_param_sorts();
    std::string name = sort->get_uninterpreted_name();
    if (param_sorts.empty())
    {
      return uninterpreted_sort(name, 0);
    }
    SortVec transferred;
    for (const Sort & s : param_sorts)
    {
      transferred.push_back(transfer_sort(s));
    }
    return term_builder->make_sort(uninterpreted_sort(name, param_sorts.size()),
                                   transferred);
  }
  else if (sk == SortKind::UNINTERPRETED_CONS)
  {
    return uninterpreted_sort(sort->get_uninterpreted_name(),
                              sort->get_arity());
  }
  else if (sk == SortKind::DATATYPE)
  {
    return transfer_datatype_sort(sort);
  }
  else
  {
    throw NotImplementedException("Failed to transfer sort: "
                                  + sort->to_string());
  }
}

Sort TermTranslator::transfer_datatype_sort(const Sort & sort)
{
  Datatype dt = sort->get_datatype();
  std::string name = dt->get_name();
  auto it = datatype_sorts.find(name);
  if (it != datatype_sorts.end())
  {
    // cache hit
    return it->second;
  }
  // a selector of another datatype that refers back to this one would
  // otherwise recurse forever
  if (!datatypes_in_progress.insert(name).second)
  {
    throw NotImplementedException(
        "Cannot transfer the mutually recursive "
        "datatype "
        + name);
  }
  try
  {
    DatatypeDecl decl = term_builder->make_datatype_decl(name);
    for (const std::string & cons : dt->get_constructor_names())
    {
      DatatypeConstructorDecl cons_decl =
          term_builder->make_datatype_constructor_decl(cons);
      for (const std::string & sel : dt->get_selector_names(cons))
      {
        Sort sel_sort = dt->get_selector_sort(cons, sel);
        if (sel_sort == sort)
        {
          term_builder->add_selector_self(cons_decl, sel);
        }
        else
        {
          term_builder->add_selector(cons_decl, sel, transfer_sort(sel_sort));
        }
      }
      term_builder->add_constructor(decl, cons_decl);
    }
    Sort res = term_builder->make_sort(decl);
    datatypes_in_progress.erase(name);
    datatype_sorts[name] = res;
    return res;
  }
  catch (...)
  {
    datatypes_in_progress.erase(name);
    throw;
  }
}

Term TermTranslator::transfer_datatype_component(const Term & term)
{
  Sort sort = term->get_sort();
  SortKind sk = sort->get_kind();
  // a constructor makes its datatype, a selector or tester takes it
  Sort dt_sort = sk == SortKind::CONSTRUCTOR ? sort->get_codomain_sort()
                                             : sort->get_domain_sorts().at(0);
  Sort transferred = transfer_sort(dt_sort);
  if (sk == SortKind::CONSTRUCTOR)
  {
    return term_builder->get_constructor(transferred,
                                         term->get_constructor_name());
  }
  if (sk == SortKind::TESTER)
  {
    return term_builder->get_tester(transferred, term->get_constructor_name());
  }
  // a selector is named together with the constructor it belongs to
  std::string name = term->get_selector_name();
  Datatype dt = dt_sort->get_datatype();
  for (const std::string & cons : dt->get_constructor_names())
  {
    for (const std::string & sel : dt->get_selector_names(cons))
    {
      if (sel == name)
      {
        return term_builder->get_selector(transferred, cons, sel);
      }
    }
  }
  throw InternalException("Failed to transfer selector " + name
                          + ": its datatype has no selector of that name");
}

Sort TermTranslator::uninterpreted_sort(const std::string & name,
                                        std::uint64_t arity)
{
  auto it = uninterpreted_sorts.find(name);
  if (it == uninterpreted_sorts.end())
  {
    Sort sort = term_builder->make_sort(name, arity);
    uninterpreted_sorts[name] = sort;
    return sort;
  }
  if (it->second->get_arity() != arity)
  {
    throw IncorrectUsageException("Sort " + name
                                  + " was transferred with arity "
                                  + std::to_string(it->second->get_arity())
                                  + ", not " + std::to_string(arity));
  }
  // cache hit
  return it->second;
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
  TermVec children;
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

      // insert in reverse order
      // helps symbols be declared in same order
      children.clear();
      children.insert(children.end(), t->begin(), t->end());
      for (auto it = children.rbegin(); it != children.rend(); it++)
      {
        to_visit.push_back(*it);
      }
    }
    else
    {
      SortKind sk = t->get_sort()->get_kind();
      if (sk == SortKind::CONSTRUCTOR || sk == SortKind::SELECTOR
          || sk == SortKind::TESTER)
      {
        cache[t] = transfer_datatype_component(t);
      }
      // a param is a symbol too, but has a param name, not a symbol name
      else if (t->is_param())
      {
        s = transfer_sort(t->get_sort());
        cache[t] = term_builder->make_param(t->get_param_name(), s);
      }
      else if (t->is_symbol())
      {
        s = transfer_sort(t->get_sort());
        std::string name = t->get_symbol_name();
        Term sym;
        try
        {
          sym = term_builder->get_symbol(name);
        }
        catch (IncorrectUsageException & e)
        {
          // not declared in this solver yet
        }

        if (!sym)
        {
          cache[t] = term_builder->make_symbol(name, s);
        }
        // An uninterpreted sort can't be looked up by name, so transfer_sort
        // makes a new one of the same name, and two that both use one are
        // let through.
        else if (s == sym->get_sort()
                 || (uses_uninterp_sort(s)
                     && uses_uninterp_sort(sym->get_sort())))
        {
          cache[t] = sym;
        }
        else
        {
          // Otherwise the symbol must cast to the expected sort.
          Sort cast_sort;
          try
          {
            cast_sort = term_builder->cast_term(sym, s)->get_sort();
          }
          catch (NotImplementedException & e)
          {
            // not castable
          }
          if (cast_sort != s)
          {
            throw IncorrectUsageException(
                "Can't transfer symbol " + name + " of sort " + s->to_string()
                + ": the target solver has it with sort "
                + sym->get_sort()->to_string());
          }
          cache[t] = sym;
        }
      }
      // a datatype value and a store chain are rebuilt below, from their
      // operator and children
      else if (t->is_value() && sk != SortKind::DATATYPE
               && t->get_op().kind() != Op::Store)
      {
        s = transfer_sort(t->get_sort());
        if (s->get_kind() == SortKind::ARRAY)
        {
          // special case for const-array
          Term val = cache.at(*(t->begin()));
          Sort valsort = val->get_sort();
          if (s->get_elemsort() != valsort)
          {
            throw NotImplementedException("Expecting element sort but got "
                                          + val->get_sort()->to_string()
                                          + " and " + s->to_string());
          }
          else if (valsort->get_kind() == SortKind::ARRAY)
          {
            throw NotImplementedException(
                "Transferring terms with multi-dimensional constant arrays is "
                "not yet supported. Please contact the developers.");
          }
          cache[t] = term_builder->make_term(val, s);
        }
        else if (sk == SortKind::BV)
        {
          cache[t] = term_builder->make_term(t->to_bits(), s, 2);
        }
        else
        {
          // pass the original sort here
          // allows us to transfer from a solver that doesn't alias sorts
          // to one that does alias sorts
          // the sort will be transferred again in value_from_smt2
          cache[t] = value_from_smt2(
              t->print_value_as(t->get_sort()->get_kind()), t->get_sort());
        }
      }
      else
      {
        Op op = t->get_op();
        if (op.is_null())
        {
          throw NotImplementedException(
              "Can't transfer " + t->to_string()
              + ": it is not a symbol, param, value or operator application");
        }

        cached_children.clear();
        for (auto c : t)
        {
          cached_children.push_back(cache.at(c));
        }

        if (!op.check_sortedness(cached_children))
        {
          cache[t] = term_builder->cast_op(op, cached_children);
        }
        else
        {
          // MathSAT and Yices2 make an integer-valued Real an Int, so an
          // equation over Reals can have an Int side, which solvers such as
          // cvc5 do not equate with a Real
          if (op.kind() == Op::Equal || op.kind() == Op::Distinct)
          {
            widen_ints(cached_children);
          }
          cache[t] = term_builder->make_term(t->get_op(), cached_children);
        }
      }
    }
  }

  // make sure the sort is as-expected and cast if not
  // for dealing with solvers that alias sorts

  return cache.at(term);
}

Term TermTranslator::transfer_term(const Term & term, const SortKind sk)
{
  Term transferred_term = transfer_term(term);
  Sort transferred_sort = transferred_term->get_sort();
  SortKind transferred_sk = transferred_sort->get_kind();
  if (transferred_sk == sk)
  {
    return transferred_term;
  }

  // only handles Bool <-> BV1, and Int <-> Real
  // otherwise throws an exception

  // expect this to be the most common case
  if (transferred_sk == SortKind::BV && transferred_sort->get_width() == 1
      && sk == SortKind::BOOL)
  {
    Sort sort = term_builder->make_sort(SortKind::BOOL);
    return term_builder->cast_term(transferred_term, sort);
  }
  else if (transferred_sk == SortKind::BOOL && sk == SortKind::BV)
  {
    Sort sort = term_builder->make_sort(SortKind::BV, 1);
    return term_builder->cast_term(transferred_term, sort);
  }
  else if (transferred_sk == SortKind::INT && sk == SortKind::REAL)
  {
    Sort sort = term_builder->make_sort(SortKind::REAL);
    return term_builder->cast_term(transferred_term, sort);
  }
  else if (transferred_sk == SortKind::REAL && sk == SortKind::INT)
  {
    Sort sort = term_builder->make_sort(SortKind::INT);
    return term_builder->cast_term(transferred_term, sort);
  }
  else if (transferred_sk == SortKind::STRING)
  {
    Sort sort = term_builder->make_sort(SortKind::STRING);
    return term_builder->cast_term(transferred_term, sort);
  }
  else
  {
    std::string msg("Cannot cast ");
    msg += transferred_term->to_string() + " to " + to_string(sk);
    throw IncorrectUsageException(msg);
  }
}

UnorderedTermMap & TermTranslator::get_cache() { return cache; }

const TermBuilder & TermTranslator::get_term_builder() const
{
  return term_builder;
}

std::string TermTranslator::infixize_rational(const std::string smtlib) const
{
  // smtlib: (/ up down)
  // ind -- index
  std::string op;
  std::string::size_type ind_of_up_start = smtlib.find_first_of("/");
  // not a fraction, or already infix, as Yices2 prints one ("a/b")
  if (ind_of_up_start == std::string::npos || smtlib.front() != '(')
  {
    return smtlib;
  }
  ind_of_up_start += 2;
  op = "/";
  std::string new_up;
  std::string::size_type ind_of_up_end;
  const std::string malformed = "Can't read " + smtlib + " as a rational.";
  if (smtlib.substr(ind_of_up_start, 2) == "(-")
  {
    ind_of_up_end = smtlib.find_first_of(')', ind_of_up_start);
    if (ind_of_up_end == std::string::npos)
    {
      throw IncorrectUsageException(malformed);
    }
    new_up = "- "
             + smtlib.substr(ind_of_up_start + 3,
                             ind_of_up_end - ind_of_up_start - 3);
  }
  else
  {
    ind_of_up_end = smtlib.find_first_of(' ', ind_of_up_start);
    if (ind_of_up_end == std::string::npos)
    {
      throw IncorrectUsageException(malformed);
    }
    ind_of_up_end -= 1;
    new_up =
        smtlib.substr(ind_of_up_start, ind_of_up_end - ind_of_up_start + 1);
  }
  std::string::size_type ind_of_down_start = ind_of_up_end + 2;
  std::string::size_type ind_of_down_end =
      smtlib.find_first_of(')', ind_of_down_start);
  if (ind_of_down_end == std::string::npos)
  {
    throw IncorrectUsageException(malformed);
  }
  ind_of_down_end -= 1;
  std::string new_down =
      smtlib.substr(ind_of_down_start, ind_of_down_end - ind_of_down_start + 1);
  // Z3 prints the numerator and denominator as integral decimals ("1.0"),
  // which a fraction of numerals cannot have
  auto drop_point_zeros = [](std::string & num) {
    std::string::size_type point = num.find('.');
    if (point != std::string::npos
        && num.find_first_not_of('0', point + 1) == std::string::npos)
    {
      num.erase(point);
    }
  };
  drop_point_zeros(new_up);
  drop_point_zeros(new_down);
  std::string new_string = new_up + " " + op + " " + new_down;
  return new_string;
}

Term TermTranslator::value_from_smt2(const std::string val,
                                     const Sort orig_sort)
{
  SortKind sk = orig_sort->get_kind();
  Sort sort = transfer_sort(orig_sort);
  if (sk == SortKind::BV)
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
      return term_builder->make_term(bvval, sort, 10);
    }
    else if (prefix == "#b")
    {
      bvval = val.substr(2, val.length() - 2);
      return term_builder->make_term(bvval, sort, 2);
    }
    else if (prefix == "#x")
    {
      bvval = val.substr(2, val.length() - 2);
      return term_builder->make_term(bvval, sort, 16);
    }
    else
    {
      throw IncorrectUsageException("Can't read " + val
                                    + " as a bit-vector sort.");
    }
  }
  else if ((sk == SortKind::INT) || (sk == SortKind::REAL))
  {
    if (val.substr(0, 2) == "(-")
    {
      std::string posval = val.substr(3, val.length() - 4);
      posval = infixize_rational(posval);
      Term posterm = term_builder->make_term(posval, sort);
      return term_builder->make_term(Op::Negate, posterm);
    }
    else
    {
      std::string mval = infixize_rational(val);
      if (mval.substr(0, 2) == "- ")
      {
        std::string posval = mval.substr(2, mval.length() - 2);
        Term posterm = term_builder->make_term(posval, sort);
        return term_builder->make_term(Op::Negate, posterm);
      }
      return term_builder->make_term(mval, sort);
    }
  }
  // this check HAS to come after bit-vector check
  // because boolector aliases those two sorts
  else if (sk == SortKind::BOOL)
  {
    if (val != "true" && val != "false")
    {
      throw IncorrectUsageException("Unexpected boolean value: " + val);
    }
    else
    {
      return term_builder->make_term(val == "true");
    }
  }
  else if (sk == SortKind::STRING)
  {
    // The SMT-LIB representation of a string will be wrapped in double quotes.
    // These need to be stripped.
    std::string strval = val.substr(1, val.size() - 2);
    // Additionally, SMT-LIB escapes internal double quotes by doubling them.
    // We need to replace them each by a single double quote.
    std::string::size_type startpos = 0;
    while (startpos < strval.size())
    {
      auto pos = strval.find("\"\"", startpos);
      if (pos == strval.npos)
      {
        break;
      }
      strval.erase(pos, 1);
      startpos = pos + 1;
    }
    return term_builder->make_term(strval, true, sort);
  }
  {
    throw NotImplementedException(
        "Only taking bool, bv, int, real, str value terms currently.");
  }
}

void TermTranslator::widen_ints(TermVec & terms) const
{
  if (std::any_of(terms.begin(), terms.end(), [](const Term & t) {
        return t->get_sort()->get_kind() == SortKind::REAL;
      }))
  {
    Sort realsort = term_builder->make_sort(SortKind::REAL);
    for (Term & t : terms)
    {
      if (t->get_sort()->get_kind() == SortKind::INT)
      {
        t = term_builder->cast_term(t, realsort);
      }
    }
  }
}

}  // namespace smt
