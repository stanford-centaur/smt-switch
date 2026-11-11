/*!
 * \file cvc5_solver.cpp
 * \brief cvc5 implementation of AbsSmtSolver
 * \author Makai Mann
 * \author Áron Ricardo Perez-Lopez
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/cvc5_solver.h"

#include <cstddef>
#include <cstdint>
#include <exception>
#include <fstream>
#include <memory>
#include <sstream>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

#include "smt-switch/cvc5_datatype.h"
#include "smt-switch/cvc5_sort.h"
#include "smt-switch/cvc5_term.h"
#include "smt-switch/datatype.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/result.h"
#include "smt-switch/solver_enums.h"
#include "smt-switch/solver_utils.h"
#include "smt-switch/utils.h"

namespace smt {

// The cvc5 sort of a term of sort s. cvc5 accepts a sort constructor there
// and goes on with it, so it is refused here.
static ::cvc5::Sort term_sort(const Sort & s)
{
  auto cs = backend_pointer_cast<Cvc5Sort>(s)->get_cvc5_sort();
  if (cs.isUninterpretedSortConstructor())
  {
    throw IncorrectUsageException("Sort constructor "
                                  + s->get_uninterpreted_name()
                                  + " is not a term sort until it is applied");
  }
  return cs;
}

/* Cvc5Solver implementation */

// the options every Cvc5Solver starts from, set again by reset()
static void set_default_options(::cvc5::Solver & s)
{
  s.setOption("lang", "smt2");
  s.setOption("bv-print-consts-as-indexed-symbols", "true");
  s.setOption("arrays-exp", "true");
}

struct Cvc5Solver::Instance
{
  Instance() : solver(tm) { set_default_options(solver); }

  cvc5::TermManager tm = {};
  cvc5::Solver solver;
};

Cvc5Solver::Cvc5Solver()
    : AbsSmtSolver(CVC5), instance(std::make_shared<Instance>())
{
}

void Cvc5Solver::set_opt(const std::string option, const std::string value)
{
  std::string cvc5option = option;
  std::string cvc5value = value;
  if (option == "time-limit")
  {
    cvc5option = "tlimit-per";
    cvc5value = std::to_string(time_limit_milliseconds(value));
  }

  try
  {
    instance->solver.setOption(cvc5option, cvc5value);
  }
  catch (::cvc5::CVC5ApiUnsupportedException &)
  {
    throw NotImplementedException("cvc5 does not support the option " + option);
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    // a value cvc5 does not allow, or an option it no longer takes
    throw IncorrectUsageException(e.what());
  }
}

void Cvc5Solver::set_logic(const std::string logic)
{
  // cvc5 reads an empty name, or a prefix such as QF_ with no theory after
  // it, as propositional logic, which no logic name means. Its other names
  // beyond SMT-LIB's, such as HORN, are its own extensions.
  if (logic.empty() || logic.back() == '_')
  {
    throw IncorrectUsageException(logic + " is not a logic");
  }
  // cvc5 refuses an unknown logic, a second one and one after the first
  // assertion, check or push
  try
  {
    instance->solver.setLogic(logic);
  }
  catch (cvc5::CVC5ApiException & e)
  {
    // All three are the same exception, but a fresh solver can refuse only
    // the logic itself.
    cvc5::Solver fresh(instance->tm);
    try
    {
      fresh.setLogic(logic);
    }
    catch (cvc5::CVC5ApiException &)
    {
      if (!is_smtlib_logic(logic))
      {
        throw IncorrectUsageException(logic + " is not a logic");
      }
      throw NotImplementedException("cvc5 does not support the logic " + logic);
    }
    throw IncorrectUsageException(e.what());
  }
}

Term Cvc5Solver::make_term(bool b) const
{
  try
  {
    return std::make_shared<Cvc5Term>(instance->tm.mkBoolean(b));
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term Cvc5Solver::make_term(int64_t i, const Sort & sort) const
{
  try
  {
    SortKind sk = sort->get_sort_kind();
    ::cvc5::Term c;

    if (sk == INT)
    {
      c = instance->tm.mkInteger(i);
    }
    else if (sk == REAL)
    {
      c = instance->tm.mkReal(i);
    }
    else if (sk == BV)
    {
      // cvc5 uses unsigned integers for mkBitVector
      // to avoid casting issues, always use a string in base 10
      std::string sval = std::to_string(i);
      c = instance->tm.mkBitVector(narrow_width(sort->get_width()), sval, 10);
    }
    else
    {
      throw IncorrectUsageException("Can't make a numeric constant of sort "
                                    + sort->to_string());
    }

    return std::make_shared<Cvc5Term>(c);
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    // pretty safe to assume that an error is due to incorrect usage
    throw IncorrectUsageException(e.what());
  }
}

Term Cvc5Solver::make_term(const std::string & s,
                           bool useEscSequences,
                           const Sort & sort) const
{
  try
  {
    SortKind sk = sort->get_sort_kind();
    ::cvc5::Term c;

    if (sk == STRING)
    {
      c = instance->tm.mkString(s, useEscSequences);
    }
    else
    {
      throw IncorrectUsageException("Can't make a string constant of sort "
                                    + sort->to_string());
    }

    return std::make_shared<Cvc5Term>(c);
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw IncorrectUsageException(e.what());
  }
}

Term Cvc5Solver::make_term(const std::wstring & s, const Sort & sort) const
{
  try
  {
    SortKind sk = sort->get_sort_kind();
    ::cvc5::Term c;

    if (sk == STRING)
    {
      c = instance->tm.mkString(std::u32string(s.begin(), s.end()));
    }
    else
    {
      throw IncorrectUsageException("Can't make a string constant of sort "
                                    + sort->to_string());
    }

    return std::make_shared<Cvc5Term>(c);
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw IncorrectUsageException(e.what());
  }
}

Term Cvc5Solver::make_term(std::string val,
                           const Sort & sort,
                           uint64_t base) const
{
  try
  {
    SortKind sk = sort->get_sort_kind();
    ::cvc5::Term c;

    if ((sk == INT) || (sk == REAL))
    {
      std::string decimal = arith_value_to_decimal(sk, val, base);
      if (sk == INT)
      {
        c = instance->tm.mkInteger(decimal);
      }
      else
      {
        c = instance->tm.mkReal(decimal);
      }
    }
    else if (sk == BV)
    {
      std::uint32_t width = narrow_width(sort->get_width());
      c = width <= 64 ? instance->tm.mkBitVector(
                            width, detail::bv_value_to_uint64(val, base, width))
                      : instance->tm.mkBitVector(
                            width, bv_value_to_bits(val, base, sort), 2);
    }
    else
    {
      throw IncorrectUsageException("Can't make a numeric constant of sort "
                                    + sort->to_string());
    }

    return std::make_shared<Cvc5Term>(c);
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    // pretty safe to assume that an error is due to incorrect usage
    throw IncorrectUsageException(e.what());
  }
}

Term Cvc5Solver::make_term(const Term & val, const Sort & sort) const
{
  std::shared_ptr<Cvc5Term> cterm = backend_pointer_cast<Cvc5Term>(val);
  std::shared_ptr<Cvc5Sort> csort = backend_pointer_cast<Cvc5Sort>(sort);
  ::cvc5::Term const_arr = instance->tm.mkConstArray(csort->sort, cterm->term);
  return std::make_shared<Cvc5Term>(const_arr);
}

void Cvc5Solver::do_assert(const Term & t)
{
  try
  {
    std::shared_ptr<Cvc5Term> cterm = backend_pointer_cast<Cvc5Term>(t);
    instance->solver.assertFormula(cterm->term);
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Result Cvc5Solver::check_sat()
{
  try
  {
    ::cvc5::Result r = instance->solver.checkSat();
    if (r.isUnsat())
    {
      return Result(UNSAT);
    }
    else if (r.isSat())
    {
      return Result(SAT);
    }
    else if (r.isUnknown())
    {
      std::stringstream ss;
      ss << r.getUnknownExplanation();
      return Result(UNKNOWN, ss.str());
    }
    else
    {
      throw NotImplementedException(
          "cvc5 gave a result that is not sat, unsat or unknown");
    }
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Result Cvc5Solver::do_check_sat_assuming(const TermVec & assumptions)
{
  try
  {
    std::vector<::cvc5::Term> cvc5assumps;
    cvc5assumps.reserve(assumptions.size());
    for (const Term & a : assumptions)
    {
      cvc5assumps.push_back(backend_pointer_cast<Cvc5Term>(a)->term);
    }

    ::cvc5::Result r = instance->solver.checkSatAssuming(cvc5assumps);
    if (r.isUnsat())
    {
      return Result(UNSAT);
    }
    else if (r.isSat())
    {
      return Result(SAT);
    }
    else if (r.isUnknown())
    {
      std::stringstream ss;
      ss << r.getUnknownExplanation();
      return Result(UNKNOWN, ss.str());
    }
    else
    {
      throw NotImplementedException(
          "cvc5 gave a result that is not sat, unsat or unknown");
    }
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

void Cvc5Solver::do_push(uint64_t num)
{
  try
  {
    instance->solver.push(narrow_levels(num));
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

void Cvc5Solver::do_pop(uint64_t num)
{
  try
  {
    instance->solver.pop(narrow_levels(num));
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term Cvc5Solver::get_value(const Term & t) const
{
  try
  {
    std::shared_ptr<Cvc5Term> cterm = backend_pointer_cast<Cvc5Term>(t);
    return std::make_shared<Cvc5Term>(instance->solver.getValue(cterm->term));
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

UnorderedTermMap Cvc5Solver::get_array_values(const Term & arr,
                                              Term & out_const_base) const
{
  try
  {
    out_const_base = nullptr;
    cvc5::Term carr = backend_pointer_cast<Cvc5Term>(arr)->term;
    // get the array value
    // cvc5 returns a sequence of stores
    carr = instance->solver.getValue(carr);

    std::vector<std::pair<Term, Term>> stores;
    while (carr.hasOp() && carr.getKind() == cvc5::Kind::STORE)
    {
      stores.push_back(
          { Term(new Cvc5Term(carr[1])), Term(new Cvc5Term(carr[2])) });
      carr = carr[0];
    }

    if (carr.getKind() == cvc5::Kind::CONST_ARRAY)
    {
      out_const_base = Term(new Cvc5Term(carr.getConstArrayBase()));
    }

    return store_chain_values(stores);
  }
  catch (cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

void Cvc5Solver::get_unsat_assumptions(UnorderedTermSet & out) const
{
  Term f;
  try
  {
    for (auto cterm : instance->solver.getUnsatAssumptions())
    {
      out.insert(std::make_shared<Cvc5Term>(cterm));
    }
  }
  // this function seems to return a different exception type
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
}

Sort Cvc5Solver::make_sort(const std::string name, uint64_t arity) const
{
  try
  {
    return std::make_shared<Cvc5Sort>(instance->solver.declareSort(
        name, detail::narrow<uint32_t>(arity, "a number of sort parameters")));
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Sort Cvc5Solver::make_sort(SortKind sk) const
{
  try
  {
    if (sk == BOOL)
    {
      return std::make_shared<Cvc5Sort>(instance->tm.getBooleanSort());
    }
    else if (sk == INT)
    {
      return std::make_shared<Cvc5Sort>(instance->tm.getIntegerSort());
    }
    else if (sk == REAL)
    {
      return std::make_shared<Cvc5Sort>(instance->tm.getRealSort());
    }
    else if (sk == STRING)
    {
      return std::make_shared<Cvc5Sort>(instance->tm.getStringSort());
    }
    else
    {
      throw IncorrectUsageException("Can't make a sort of kind " + to_string(sk)
                                    + " without arguments");
    }
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Sort Cvc5Solver::make_sort(SortKind sk, uint64_t size) const
{
  try
  {
    if (sk == BV)
    {
      return std::make_shared<Cvc5Sort>(
          instance->tm.mkBitVectorSort(narrow_width(size)));
    }
    else
    {
      throw IncorrectUsageException("Can't make a sort of kind " + to_string(sk)
                                    + " from an integer");
    }
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Sort Cvc5Solver::make_sort(SortKind sk, const SortVec & sorts) const
{
  try
  {
    if (sk == FUNCTION)
    {
      if (sorts.size() < 2)
      {
        throw IncorrectUsageException(
            "A function sort needs at least two sorts");
      }

      // arity is one less, because last sort is return sort
      size_t arity = sorts.size() - 1;

      std::vector<::cvc5::Sort> csorts;
      csorts.reserve(arity);
      ::cvc5::Sort csort;
      for (size_t i = 0; i < arity; i++)
      {
        csort = term_sort(sorts[i]);
        csorts.push_back(csort);
      }

      csort = term_sort(sorts.back());
      ::cvc5::Sort cfunsort = instance->tm.mkFunctionSort(csorts, csort);
      return std::make_shared<Cvc5Sort>(cfunsort);
    }
    else if (sk == ARRAY && sorts.size() == 2)
    {
      return std::make_shared<Cvc5Sort>(
          instance->tm.mkArraySort(term_sort(sorts[0]), term_sort(sorts[1])));
    }
    else
    {
      throw IncorrectUsageException("Can't make a sort of kind " + to_string(sk)
                                    + " from " + std::to_string(sorts.size())
                                    + " sorts");
    }
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Sort Cvc5Solver::make_sort(const Sort & sort_con, const SortVec & sorts) const
{
  ::cvc5::Sort csort_con = backend_pointer_cast<Cvc5Sort>(sort_con)->sort;
  if (!csort_con.isUninterpretedSortConstructor())
  {
    throw IncorrectUsageException("Sort " + sort_con->to_string()
                                  + " is not a sort constructor");
  }

  size_t numsorts = sorts.size();
  size_t arity = csort_con.getUninterpretedSortConstructorArity();
  if (numsorts != arity)
  {
    throw IncorrectUsageException("Expected " + std::to_string(arity)
                                  + " sort arguments to " + csort_con.toString()
                                  + " but got " + std::to_string(numsorts));
  }

  std::vector<::cvc5::Sort> csorts;
  csorts.reserve(sorts.size());
  ::cvc5::Sort csort;
  for (uint32_t i = 0; i < arity; i++)
  {
    csort = term_sort(sorts[i]);
    csorts.push_back(csort);
  }

  try
  {
    return std::make_shared<Cvc5Sort>(csort_con.instantiate(csorts));
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term Cvc5Solver::make_symbol(const std::string name, const Sort & sort)
{
  // check that name is available
  // to make cvc5 behave the same as other solvers
  if (symbol_table.find(name) != symbol_table.end())
  {
    throw IncorrectUsageException("Symbol " + name + " has already been used");
  }

  try
  {
    auto t = instance->tm.mkConst(term_sort(sort), name);
    Term res = std::make_shared<::smt::Cvc5Term>(t);
    symbol_table[name] = res;
    return res;
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term Cvc5Solver::get_symbol(const std::string & name) const
{
  auto it = symbol_table.find(name);
  if (it == symbol_table.end())
  {
    throw IncorrectUsageException("Symbol named " + name + " does not exist");
  }
  return it->second;
}

Term Cvc5Solver::make_param(const std::string name, const Sort & sort) const
{
  try
  {
    auto t = instance->tm.mkVar(term_sort(sort), name);
    return std::make_shared<::smt::Cvc5Term>(t);
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Sort Cvc5Solver::make_sort(const DatatypeDecl & d) const
{
  return make_datatype_sorts({ d })[0];
}

DatatypeDecl Cvc5Solver::make_datatype_decl(const std::string & s) const
{
  try
  {
    return std::make_shared<Cvc5DatatypeDecl>(instance->tm.mkDatatypeDecl(s));
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

DatatypeConstructorDecl Cvc5Solver::make_datatype_constructor_decl(
    const std::string s) const
{
  try
  {
    return std::make_shared<Cvc5DatatypeConstructorDecl>(
        instance->tm.mkDatatypeConstructorDecl(s), s);
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

void Cvc5Solver::add_constructor(DatatypeDecl & dt,
                                 const DatatypeConstructorDecl & con) const
{
  try
  {
    std::shared_ptr<Cvc5DatatypeDecl> cdt =
        backend_pointer_cast<Cvc5DatatypeDecl>(dt);
    std::shared_ptr<Cvc5DatatypeConstructorDecl> ccon =
        backend_pointer_cast<Cvc5DatatypeConstructorDecl>(con);
    cdt->datatypedecl.addConstructor(ccon->datatypeconstructordecl);
    cdt->constructors.push_back(ccon);
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

void Cvc5Solver::add_selector(DatatypeConstructorDecl & dt,
                              const std::string & name,
                              const Sort & s) const
{
  try
  {
    std::shared_ptr<Cvc5DatatypeConstructorDecl> cdt =
        backend_pointer_cast<Cvc5DatatypeConstructorDecl>(dt);
    auto cs = term_sort(s);
    cdt->datatypeconstructordecl.addSelector(name, cs);
    cdt->selectors.emplace_back(name, cs);
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

void Cvc5Solver::add_selector_self(DatatypeConstructorDecl & dt,
                                   const std::string & name) const
{
  try
  {
    std::shared_ptr<Cvc5DatatypeConstructorDecl> cdt =
        backend_pointer_cast<Cvc5DatatypeConstructorDecl>(dt);
    cdt->datatypeconstructordecl.addSelectorSelf(name);
    cdt->selectors.emplace_back(name, cvc5::Sort());
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term Cvc5Solver::get_constructor(const Sort & s, std::string name) const
{
  try
  {
    std::shared_ptr<Cvc5Sort> cs = backend_pointer_cast<Cvc5Sort>(s);
    cvc5::Datatype dt = cs->get_cvc5_datatype();
    for (size_t i = 0; i != dt.getNumConstructors(); i++)
    {
      cvc5::DatatypeConstructor ct = dt[i];
      if (ct.getName() == name)
      {
        return std::make_shared<Cvc5Term>(ct.getTerm());
      }
    }
    throw IncorrectUsageException(name + " is not a constructor of "
                                  + cs->sort.toString());
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term Cvc5Solver::get_tester(const Sort & s, std::string name) const
{
  try
  {
    std::shared_ptr<Cvc5Sort> cs = backend_pointer_cast<Cvc5Sort>(s);
    cvc5::Datatype dt = cs->get_cvc5_datatype();
    for (size_t i = 0; i != dt.getNumConstructors(); i++)
    {
      cvc5::DatatypeConstructor ct = dt[i];
      if (ct.getName() == name)
      {
        return std::make_shared<Cvc5Term>(ct.getTesterTerm());
      }
    }
    throw IncorrectUsageException(name + " is not a constructor of "
                                  + cs->sort.toString());
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term Cvc5Solver::get_selector(const Sort & s,
                              std::string con,
                              std::string name) const
{
  try
  {
    std::shared_ptr<Cvc5Sort> cs = backend_pointer_cast<Cvc5Sort>(s);
    cvc5::Datatype dt = cs->get_cvc5_datatype();
    for (size_t i = 0; i != dt.getNumConstructors(); i++)
    {
      cvc5::DatatypeConstructor ct = dt[i];
      if (ct.getName() != con)
      {
        continue;
      }
      for (size_t j = 0; j != ct.getNumSelectors(); j++)
      {
        cvc5::DatatypeSelector sel = ct[j];
        if (sel.getName() == name)
        {
          return std::make_shared<Cvc5Term>(sel.getTerm());
        }
      }
    }
    throw IncorrectUsageException(name + " is not a selector of constructor "
                                  + con + " of " + cs->sort.toString());
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

cvc5::DatatypeDecl Cvc5Solver::fresh_datatype_decl(
    const Cvc5DatatypeDecl & d) const
{
  auto fresh = instance->tm.mkDatatypeDecl(d.get_name());
  for (const auto & con : d.constructors)
  {
    auto fresh_con = instance->tm.mkDatatypeConstructorDecl(con->name);
    for (const auto & sel : con->selectors)
    {
      if (sel.second.isNull())
      {
        fresh_con.addSelectorSelf(sel.first);
      }
      else
      {
        fresh_con.addSelector(sel.first, sel.second);
      }
    }
    fresh.addConstructor(fresh_con);
  }
  return fresh;
}

SortVec Cvc5Solver::make_datatype_sorts(
    const std::vector<DatatypeDecl> & decls) const
{
  try
  {
    SortVec dt_sorts;
    dt_sorts.reserve(decls.size());

    std::vector<std::shared_ptr<Cvc5DatatypeDecl>> cvc5_decl_wrappers;
    std::vector<cvc5::DatatypeDecl> cvc5_decls;
    cvc5_decls.reserve(decls.size());
    for (const auto & d : decls)
    {
      auto cd = backend_pointer_cast<Cvc5DatatypeDecl>(d);
      // as SMT-LIB declares a datatype once
      if (cd->used)
      {
        throw IncorrectUsageException("Datatype declaration " + cd->get_name()
                                      + " was used for a sort already");
      }
      cvc5_decl_wrappers.push_back(cd);
      cvc5_decls.push_back(fresh_datatype_decl(*cd));
    }

    for (const auto & csort : instance->tm.mkDatatypeSorts(cvc5_decls))
    {
      dt_sorts.push_back(std::make_shared<Cvc5Sort>(csort));
    }
    for (const auto & cd : cvc5_decl_wrappers)
    {
      cd->used = true;
    }
    return dt_sorts;
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term Cvc5Solver::make_term(Op op, const TermVec & terms) const
{
  if (terms.empty())
  {
    throw IncorrectUsageException("Can't apply " + op.to_string()
                                  + " to zero terms");
  }
  else if (op.prim_op == Forall || op.prim_op == Exists)
  {
    check_quantifier_binders(op, terms);
  }
  else if (op.prim_op == Divisible && op.indices[0] < 1)
  {
    throw IncorrectUsageException(
        "Can't apply divisible with an index less than 1");
  }
  // Operators that SMT-LIB applies to more than two arguments, but that cvc5
  // only applies to two
  else if (terms.size() > 2 && (op.prim_op == StrLt || op.prim_op == StrLeq))
  {
    return make_nary_term(this, op, terms);
  }

  try
  {
    std::vector<cvc5::Term> cterms;
    cterms.reserve(terms.size());
    std::shared_ptr<Cvc5Term> cterm;
    for (auto t : terms)
    {
      cterm = backend_pointer_cast<Cvc5Term>(t);
      cterms.push_back(cterm->term);
    }
    // cvc5 solves a power only for a constant nonnegative exponent
    if (op.prim_op == Pow && cterms.size() == 2
        && (!cterms[1].isIntegerValue()
            || cterms[1].getIntegerValue().front() == '-'))
    {
      throw NotImplementedException(
          "cvc5 can only raise to a constant non-negative integer exponent");
    }
    if (op.prim_op == Forall || op.prim_op == Exists)
    {
      cvc5::Kind quant_kind = to_cvc5_kind(op.prim_op);
      cvc5::Term quant_res = cterms.back();
      cterms.pop_back();
      // Bind the parameters one at a time, which makes traversal easier
      // since smt-switch has no VARIABLE_LIST equivalent.
      while (cterms.size())
      {
        cvc5::Term bound_var =
            instance->tm.mkTerm(cvc5::Kind::VARIABLE_LIST, { cterms.back() });
        cterms.pop_back();
        quant_res = instance->tm.mkTerm(quant_kind, { bound_var, quant_res });
      }
      return std::make_shared<Cvc5Term>(quant_res);
    }
    else if (op.indices.empty())
    {
      return std::make_shared<Cvc5Term>(
          instance->tm.mkTerm(to_cvc5_kind(op.prim_op), cterms));
    }
    else
    {
      cvc5::Op cvc5_op = make_cvc5_op(op);
      return std::make_shared<Cvc5Term>(instance->tm.mkTerm(cvc5_op, cterms));
    }
  }
  catch (cvc5::CVC5ApiException & e)
  {
    throw IncorrectUsageException(e.what());
  }
}

void Cvc5Solver::do_reset()
{
  // cvc5 has no public reset, so start again with a new term manager and
  // solver. Each cvc5 term and sort holds a shared pointer to the node
  // manager that stores it, so terms still held from before stay valid after
  // the old term manager is destroyed, but the new solver refuses them.
  instance = std::make_shared<Instance>();
  symbol_table.clear();
}

void Cvc5Solver::do_reset_assertions()
{
  try
  {
    instance->solver.resetAssertions();
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term Cvc5Solver::substitute(const Term term,
                            const UnorderedTermMap & substitution_map) const
{
  std::vector<::cvc5::Term> keys;
  std::vector<::cvc5::Term> values;
  keys.reserve(substitution_map.size());
  values.reserve(substitution_map.size());

  for (const auto & elem : substitution_map)
  {
    keys.push_back(backend_pointer_cast<Cvc5Term>(elem.first)->term);
    values.push_back(backend_pointer_cast<Cvc5Term>(elem.second)->term);
  }

  ::cvc5::Term cterm = backend_pointer_cast<Cvc5Term>(term)->term;
  return std::make_shared<Cvc5Term>(cterm.substitute(keys, values));
}

void Cvc5Solver::dump_smt2(std::string filename) const
{
  TermVec assertions;
  for (const ::cvc5::Term & a : instance->solver.getAssertions())
  {
    assertions.push_back(std::make_shared<Cvc5Term>(a));
  }
  std::ofstream out(filename);
  smtlib_benchmark(
      out,
      instance->solver.isLogicSet() ? instance->solver.getLogic() : "ALL",
      assertions);
}

/**
   Helper function for creating a cvc5 Op from an Op
   Preconditions: op must be indexed, i.e. op.indices is not empty
*/
cvc5::Op Cvc5Solver::make_cvc5_op(Op op) const
{
  std::vector<std::uint32_t> indices;
  for (std::uint64_t index : op.indices)
  {
    indices.push_back(narrow_index(op, index));
  }
  return instance->tm.mkOp(to_cvc5_kind(op.prim_op), indices);
}

std::shared_ptr<cvc5::Solver> Cvc5Solver::get_cvc5_solver()
{
  return std::shared_ptr<cvc5::Solver>(instance, &instance->solver);
}

std::shared_ptr<cvc5::TermManager> Cvc5Solver::get_term_manager()
{
  return std::shared_ptr<cvc5::TermManager>(instance, &instance->tm);
}

/* end Cvc5Solver implementation */

}  // namespace smt
