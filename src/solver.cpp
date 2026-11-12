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

#include <cstdint>
#include <list>
#include <string>
#include <vector>

#include "smt-switch/exceptions.h"
#include "smt-switch/result.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

namespace smt {

// TODO: Implement a generic visitor

AbsSmtSolver::AbsSmtSolver(SolverKind solver_kind) : backend_kind(solver_kind)
{
}

AbsSmtSolver::AbsSmtSolver(SolverEnum se)
    : AbsSmtSolver(detail::solver_kind(se))
{
}

void AbsSmtSolver::assert_formula(const Term & t)
{
  // compares sorts rather than kinds, as some solvers alias Bool to another
  // sort
  if (!t)
  {
    throw IncorrectUsageException("Cannot assert a null term");
  }
  if (t->get_sort() != make_sort(BOOL))
  {
    throw IncorrectUsageException("Expecting a Boolean assertion but got: "
                                  + t->to_string());
  }
  do_assert(t);
}

Result AbsSmtSolver::check_sat_assuming(const TermVec & assumptions)
{
  // Every assumption is checked before any is assumed: one assumed before a
  // refused one would still hold for the next check. The check compares
  // sorts rather than kinds, as some solvers alias Bool to another sort.
  const Sort boolsort = make_sort(BOOL);
  for (const Term & a : assumptions)
  {
    if (!a)
    {
      throw IncorrectUsageException("Cannot assume a null term");
    }
    if (a->get_sort() != boolsort)
    {
      throw IncorrectUsageException("Expecting Boolean assumptions but got: "
                                    + a->to_string());
    }
  }
  return do_check_sat_assuming(assumptions);
}

Result AbsSmtSolver::check_sat_assuming_list(const TermList & assumptions)
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

std::uint64_t AbsSmtSolver::get_context_level() const { return context_level; }

void AbsSmtSolver::pop_all() { pop(get_context_level()); }

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

Sort AbsSmtSolver::make_sort(const DatatypeDecl & /* d */) const
{
  throw NotImplementedException("Datatypes are not supported by "
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

SortVec AbsSmtSolver::make_datatype_sorts(
    const std::vector<DatatypeDecl> & /* decls */) const
{
  throw NotImplementedException("make_datatype_sorts is not implemented by "
                                + to_string(backend_kind));
}

void AbsSmtSolver::dump_smt2(std::string /* filename */) const
{
  throw NotImplementedException("Dumping to a file is not supported by "
                                + to_string(backend_kind));
}

SolverKind AbsSmtSolver::get_kind() const { return backend_kind; }

SolverEnum AbsSmtSolver::get_solver_enum() const
{
  return detail::solver_enum(backend_kind);
}

}  // namespace smt
