/*!
 * \file solver.cpp
 * \brief Abstract interface for SMT solvers
 * \author Makai Mann
 * \author Clark Barrett
 * \author Áron Ricardo Perez-Lopez
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/solver.h"

#include <cstddef>
#include <cstdint>
#include <list>
#include <memory>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "smt-switch/exceptions.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

namespace smt {

AbsSmtSolver::AbsSmtSolver(solvers::Kind kind) : backend_kind(kind) {}

solvers::Kind AbsSmtSolver::get_kind() const { return backend_kind; }

void AbsSmtSolver::assert_formula(const Term & t)
{
  // compares sorts rather than kinds, as some solvers alias Bool to another
  // sort
  if (!t)
  {
    throw IncorrectUsageException("Cannot assert a null term");
  }
  if (t->get_sort() != make_sort(SortKind::BOOL))
  {
    throw IncorrectUsageException("Expecting a Boolean assertion but got: "
                                  + t->to_string());
  }
  do_assert(t);
}

Result AbsSmtSolver::check_sat_assuming(const TermVec & assumptions)
{
  // Every assumption is checked before any is assumed: one assumed before a
  // refused one would still hold for the next check.
  for (const Term & a : assumptions)
  {
    if (!a)
    {
      throw IncorrectUsageException("Cannot assume a null term");
    }
    if (!a->get_sort()->is_boolean())
    {
      throw IncorrectUsageException("Expecting Boolean assumptions but got: "
                                    + a->to_string());
    }
  }
  return do_check_sat_assuming(assumptions);
}

Result AbsSmtSolver::check_sat_assuming_list(
    const std::list<Term> & assumptions)
{
  return check_sat_assuming(assumptions);
}

Result AbsSmtSolver::check_sat_assuming_set(
    const UnorderedTermSet & assumptions)
{
  return check_sat_assuming(assumptions);
}

void AbsSmtSolver::push(std::uint64_t num)
{
  do_push(num);
  context_level += num;
}

void AbsSmtSolver::pop(std::uint64_t num)
{
  if (num > get_context_level())
  {
    throw IncorrectUsageException("Can't pop " + std::to_string(num)
                                  + " contexts at context level "
                                  + std::to_string(get_context_level()));
  }
  do_pop(num);
  context_level -= num;
}

void AbsSmtSolver::pop_all() { pop(get_context_level()); }

std::uint64_t AbsSmtSolver::get_context_level() const { return context_level; }

void AbsSmtSolver::reset()
{
  do_reset();
  context_level = 0;
}

void AbsSmtSolver::reset_assertions()
{
  do_reset_assertions();
  context_level = 0;
}

void AbsSmtSolver::dump_smt2(std::string /* filename */) const
{
  throw NotImplementedException("Dumping to a file is not supported by "
                                + to_string(backend_kind));
}

Term AbsSmtSolver::make_term(const std::string & /* s */,
                             bool /* useEscSequences */,
                             const Sort & /* sort */) const
{
  throw NotImplementedException("Strings are not supported by "
                                + to_string(backend_kind));
}

Term AbsSmtSolver::make_term(const std::wstring & /* s */,
                             const Sort & /* sort */) const
{
  throw NotImplementedException("Strings are not supported by "
                                + to_string(backend_kind));
}

DatatypeDecl AbsSmtSolver::make_datatype_decl(const std::string & /* s */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(backend_kind));
}

DatatypeConstructorDecl AbsSmtSolver::make_datatype_constructor_decl(
    const std::string /* s */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(backend_kind));
}

void AbsSmtSolver::add_constructor(
    DatatypeDecl & /* dt */, const DatatypeConstructorDecl & /* con */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(backend_kind));
}

void AbsSmtSolver::add_selector(DatatypeConstructorDecl & /* dt */,
                                const std::string & /* name */,
                                const Sort & /* s */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(backend_kind));
}

void AbsSmtSolver::add_selector_self(DatatypeConstructorDecl & /* dt */,
                                     const std::string & /* name */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(backend_kind));
}

Sort AbsSmtSolver::make_sort(const DatatypeDecl & /* d */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(backend_kind));
}

SortVec AbsSmtSolver::make_datatype_sorts(
    const std::vector<DatatypeDecl> & /* decls */) const
{
  throw NotImplementedException("make_datatype_sorts is not implemented by "
                                + to_string(backend_kind));
}

Term AbsSmtSolver::get_constructor(const Sort & /* s */,
                                   std::string /* name */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(backend_kind));
}

Term AbsSmtSolver::get_tester(const Sort & /* s */,
                              std::string /* name */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(backend_kind));
}

Term AbsSmtSolver::get_selector(const Sort & /* s */,
                                std::string /* con */,
                                std::string /* name */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(backend_kind));
}

Term AbsSmtSolver::make_nary_term(const Op & op, const TermVec & terms) const
{
  std::size_t size = terms.size();
  if (size < 2)
  {
    throw IncorrectUsageException("Can't apply " + op.to_string() + " to "
                                  + std::to_string(size) + " terms.");
  }
  if (op.is_left_assoc())
  {
    Term res = terms[0];
    for (std::size_t i = 1; i < size; ++i)
    {
      res = make_term(op, res, terms[i]);
    }
    return res;
  }
  else if (op.is_right_assoc())
  {
    Term res = terms[size - 1];
    for (std::size_t i = 1; i < size; ++i)
    {
      res = make_term(op, terms[size - 1 - i], res);
    }
    return res;
  }

  TermVec conjuncts;
  if (op.is_chainable())
  {
    for (std::size_t i = 0; i + 1 < size; ++i)
    {
      conjuncts.push_back(make_term(op, terms[i], terms[i + 1]));
    }
  }
  else if (op.is_pairwise())
  {
    for (std::size_t i = 0; i < size; ++i)
    {
      for (std::size_t j = i + 1; j < size; ++j)
      {
        conjuncts.push_back(make_term(op, terms[i], terms[j]));
      }
    }
  }
  else
  {
    throw IncorrectUsageException("Can't apply " + op.to_string() + " to "
                                  + std::to_string(size) + " terms.");
  }
  return conjuncts.size() == 1 ? conjuncts[0] : make_term(Op::And, conjuncts);
}

void AbsSmtSolver::check_quantifier_binders(const Op & op,
                                            const TermVec & terms)
{
  if (terms.size() < 2)
  {
    throw IncorrectUsageException(op.to_string()
                                  + " takes one or more params and a body");
  }
  for (std::size_t i = 0; i + 1 < terms.size(); ++i)
  {
    if (!terms[i]->is_param())
    {
      throw IncorrectUsageException(op.to_string() + " can only bind a param, "
                                    + "but got " + terms[i]->to_string());
    }
  }
}

UnorderedTermMap AbsSmtSolver::store_chain_values(
    const std::vector<std::pair<Term, Term>> & stores)
{
  UnorderedTermMap assignments;
  for (const auto & store : stores)
  {
    // insert keeps the assignment already in the map, so the outermost
    // store, which comes first, is the one that stands
    assignments.insert(store);
  }
  return assignments;
}

}  // namespace smt
