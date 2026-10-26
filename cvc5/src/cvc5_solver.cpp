/*********************                                                        */
/*! \file cvc5_solver.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief cvc5 implementation of AbsSmtSolver
**
**
**/
#include "cvc5_solver.h"

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <limits>
#include <memory>
#include <string>
#include <unordered_set>

#include "smt.h"
#include "solver_utils.h"
#include "utils.h"

namespace smt {

/* cvc5 Op mappings */
const std::unordered_map<PrimOp, ::cvc5::Kind> primop2kind(
    { { And, ::cvc5::Kind::AND },
      { Or, ::cvc5::Kind::OR },
      { Xor, ::cvc5::Kind::XOR },
      { Not, ::cvc5::Kind::NOT },
      { Implies, ::cvc5::Kind::IMPLIES },
      { Ite, ::cvc5::Kind::ITE },
      { Equal, ::cvc5::Kind::EQUAL },
      { Distinct, ::cvc5::Kind::DISTINCT },
      /* Uninterpreted Functions */
      { Apply, ::cvc5::Kind::APPLY_UF },
      /* Arithmetic Theories */
      { Plus, ::cvc5::Kind::ADD },
      { Minus, ::cvc5::Kind::SUB },
      { Negate, ::cvc5::Kind::NEG },
      { Mult, ::cvc5::Kind::MULT },
      { Div, ::cvc5::Kind::DIVISION },
      { IntDiv, ::cvc5::Kind::INTS_DIVISION },
      { Lt, ::cvc5::Kind::LT },
      { Le, ::cvc5::Kind::LEQ },
      { Gt, ::cvc5::Kind::GT },
      { Ge, ::cvc5::Kind::GEQ },
      { Mod, ::cvc5::Kind::INTS_MODULUS },
      { Abs, ::cvc5::Kind::ABS },
      { Pow, ::cvc5::Kind::POW },
      { To_Real, ::cvc5::Kind::TO_REAL },
      { To_Int, ::cvc5::Kind::TO_INTEGER },
      { Is_Int, ::cvc5::Kind::IS_INTEGER },
      /* Fixed Size BitVector Theory */
      { Concat, ::cvc5::Kind::BITVECTOR_CONCAT },
      // Indexed Op
      { Extract, ::cvc5::Kind::BITVECTOR_EXTRACT },
      { BVNot, ::cvc5::Kind::BITVECTOR_NOT },
      { BVNeg, ::cvc5::Kind::BITVECTOR_NEG },
      { BVAnd, ::cvc5::Kind::BITVECTOR_AND },
      { BVOr, ::cvc5::Kind::BITVECTOR_OR },
      { BVXor, ::cvc5::Kind::BITVECTOR_XOR },
      { BVNand, ::cvc5::Kind::BITVECTOR_NAND },
      { BVNor, ::cvc5::Kind::BITVECTOR_NOR },
      { BVXnor, ::cvc5::Kind::BITVECTOR_XNOR },
      { BVComp, ::cvc5::Kind::BITVECTOR_COMP },
      { BVAdd, ::cvc5::Kind::BITVECTOR_ADD },
      { BVSub, ::cvc5::Kind::BITVECTOR_SUB },
      { BVMul, ::cvc5::Kind::BITVECTOR_MULT },
      { BVUdiv, ::cvc5::Kind::BITVECTOR_UDIV },
      { BVSdiv, ::cvc5::Kind::BITVECTOR_SDIV },
      { BVUrem, ::cvc5::Kind::BITVECTOR_UREM },
      { BVSrem, ::cvc5::Kind::BITVECTOR_SREM },
      { BVSmod, ::cvc5::Kind::BITVECTOR_SMOD },
      { BVShl, ::cvc5::Kind::BITVECTOR_SHL },
      { BVAshr, ::cvc5::Kind::BITVECTOR_ASHR },
      { BVLshr, ::cvc5::Kind::BITVECTOR_LSHR },
      { BVUlt, ::cvc5::Kind::BITVECTOR_ULT },
      { BVUle, ::cvc5::Kind::BITVECTOR_ULE },
      { BVUgt, ::cvc5::Kind::BITVECTOR_UGT },
      { BVUge, ::cvc5::Kind::BITVECTOR_UGE },
      { BVSlt, ::cvc5::Kind::BITVECTOR_SLT },
      { BVSle, ::cvc5::Kind::BITVECTOR_SLE },
      { BVSgt, ::cvc5::Kind::BITVECTOR_SGT },
      { BVSge, ::cvc5::Kind::BITVECTOR_SGE },
      // Indexed Op
      { Zero_Extend, ::cvc5::Kind::BITVECTOR_ZERO_EXTEND },
      // Indexed Op
      { Sign_Extend, ::cvc5::Kind::BITVECTOR_SIGN_EXTEND },
      // Indexed Op
      { Repeat, ::cvc5::Kind::BITVECTOR_REPEAT },
      // Indexed Op
      { Rotate_Left, ::cvc5::Kind::BITVECTOR_ROTATE_LEFT },
      // Indexed Op
      { Rotate_Right, ::cvc5::Kind::BITVECTOR_ROTATE_RIGHT },
      // Conversion
      { BV_To_Nat, ::cvc5::Kind::BITVECTOR_UBV_TO_INT },
      { UBV_To_Int, ::cvc5::Kind::BITVECTOR_UBV_TO_INT },
      { SBV_To_Int, ::cvc5::Kind::BITVECTOR_SBV_TO_INT },
      { Int_To_BV, ::cvc5::Kind::INT_TO_BITVECTOR },
      // String Op
      { StrLt, ::cvc5::Kind::STRING_LT },
      { StrLeq, ::cvc5::Kind::STRING_LEQ },
      { StrLen, ::cvc5::Kind::STRING_LENGTH },
      { StrConcat, ::cvc5::Kind::STRING_CONCAT },
      { StrSubstr, ::cvc5::Kind::STRING_SUBSTR },
      { StrAt, ::cvc5::Kind::STRING_CHARAT },
      { StrContains, ::cvc5::Kind::STRING_CONTAINS },
      { StrIndexof, ::cvc5::Kind::STRING_INDEXOF },
      { StrReplace, ::cvc5::Kind::STRING_REPLACE },
      { StrReplaceAll, ::cvc5::Kind::STRING_REPLACE_ALL },
      { StrPrefixof, ::cvc5::Kind::STRING_PREFIX },
      { StrSuffixof, ::cvc5::Kind::STRING_SUFFIX },
      { StrIsDigit, ::cvc5::Kind::STRING_IS_DIGIT },
      // Indexed Op
      { Select, ::cvc5::Kind::SELECT },
      { Store, ::cvc5::Kind::STORE },
      { Forall, ::cvc5::Kind::FORALL },
      { Exists, ::cvc5::Kind::EXISTS },
      { Apply_Selector, ::cvc5::Kind::APPLY_SELECTOR },
      { Apply_Tester, ::cvc5::Kind::APPLY_TESTER },
      { Apply_Constructor, ::cvc5::Kind::APPLY_CONSTRUCTOR } });

// operators that SMT-LIB applies to more than two arguments, but that cvc5
// only applies to two
const std::unordered_set<PrimOp> binary_only_ops({ StrLt, StrLeq });

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

  cvc5::TermManager tm;
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
    // convert to milliseconds
    cvc5value = std::to_string(static_cast<uint64_t>(std::stod(value) * 1000));
  }

  try
  {
    instance->solver.setOption(cvc5option, cvc5value);
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

void Cvc5Solver::set_logic(const std::string logic)
{
  // cvc5 refuses an unknown logic, a second one and one after the first
  // assertion, check or push
  try
  {
    instance->solver.setLogic(logic);
  }
  catch (::cvc5::CVC5ApiException & e)
  {
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
      c = instance->tm.mkBitVector(sort->get_width(), sval, 10);
    }
    else
    {
      std::string msg = "Can't create constant with integer for sort ";
      msg += sort->to_string();
      throw IncorrectUsageException(msg.c_str());
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
      std::string msg = "Can't create a string constant for sort ";
      msg += sort->to_string();
      throw IncorrectUsageException(msg.c_str());
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
      std::string msg = "Can't create string constant for sort ";
      msg += sort->to_string();
      throw IncorrectUsageException(msg.c_str());
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
      // TODO: Only do these checks in debug
      if (base != 10)
      {
        throw IncorrectUsageException(
            "Can't use non-decimal base for reals and ints");
      }
      if (sk == INT)
      {
        c = instance->tm.mkInteger(val);
      }
      else
      {
        c = instance->tm.mkReal(val);
      }
    }
    else if (sk == BV)
    {
      c = instance->tm.mkBitVector(sort->get_width(), val, base);
    }
    else
    {
      std::string msg = "Can't create constant with integer for sort ";
      msg += sort->to_string();
      throw IncorrectUsageException(msg.c_str());
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
  std::shared_ptr<Cvc5Term> cterm = std::static_pointer_cast<Cvc5Term>(val);
  std::shared_ptr<Cvc5Sort> csort = std::static_pointer_cast<Cvc5Sort>(sort);
  ::cvc5::Term const_arr = instance->tm.mkConstArray(csort->sort, cterm->term);
  return std::make_shared<Cvc5Term>(const_arr);
}

void Cvc5Solver::assert_formula(const Term & t)
{
  try
  {
    std::shared_ptr<Cvc5Term> cterm = std::static_pointer_cast<Cvc5Term>(t);
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
      throw NotImplementedException("Unimplemented result type from cvc5");
    }
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Result Cvc5Solver::check_sat_assuming(const TermVec & assumptions)
{
  try
  {
    std::vector<::cvc5::Term> cvc5assumps;
    cvc5assumps.reserve(assumptions.size());
    for (const Term & a : assumptions)
    {
      cvc5assumps.push_back(std::static_pointer_cast<Cvc5Term>(a)->term);
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
      throw NotImplementedException("Unimplemented result type from cvc5");
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
    instance->solver.push(num);
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
    instance->solver.pop(num);
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
    std::shared_ptr<Cvc5Term> cterm = std::static_pointer_cast<Cvc5Term>(t);
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
    cvc5::Term carr = std::static_pointer_cast<Cvc5Term>(arr)->term;
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
    return std::make_shared<Cvc5Sort>(
        instance->solver.declareSort(name, arity));
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
      std::string msg("Can't create sort with sort constructor ");
      msg += to_string(sk);
      msg += " and no arguments";
      throw IncorrectUsageException(msg.c_str());
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
      return std::make_shared<Cvc5Sort>(instance->tm.mkBitVectorSort(size));
    }
    else
    {
      std::string msg("Can't create sort with sort constructor ");
      msg += to_string(sk);
      msg += " and an integer argument";
      throw IncorrectUsageException(msg.c_str());
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
            "Function sort must have >=2 sort arguments.");
      }

      // arity is one less, because last sort is return sort
      uint32_t arity = sorts.size() - 1;

      std::vector<::cvc5::Sort> csorts;
      csorts.reserve(arity);
      ::cvc5::Sort csort;
      for (uint32_t i = 0; i < arity; i++)
      {
        csort = std::static_pointer_cast<Cvc5Sort>(sorts[i])->sort;
        csorts.push_back(csort);
      }

      csort = std::static_pointer_cast<Cvc5Sort>(sorts.back())->sort;
      ::cvc5::Sort cfunsort = instance->tm.mkFunctionSort(csorts, csort);
      return std::make_shared<Cvc5Sort>(cfunsort);
    }
    else if (sk == ARRAY && sorts.size() == 2)
    {
      std::shared_ptr<Cvc5Sort> cidxsort =
          std::static_pointer_cast<Cvc5Sort>(sorts[0]);
      std::shared_ptr<Cvc5Sort> celemsort =
          std::static_pointer_cast<Cvc5Sort>(sorts[1]);
      return std::make_shared<Cvc5Sort>(
          instance->tm.mkArraySort(cidxsort->sort, celemsort->sort));
    }
    else
    {
      std::string msg("Can't create sort from sort constructor ");
      msg += to_string(sk);
      msg += " with a vector of sorts of size " + std::to_string(sorts.size());
      throw IncorrectUsageException(msg.c_str());
    }
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Sort Cvc5Solver::make_sort(const Sort & sort_con, const SortVec & sorts) const
{
  ::cvc5::Sort csort_con = std::static_pointer_cast<Cvc5Sort>(sort_con)->sort;
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
    csort = std::static_pointer_cast<Cvc5Sort>(sorts[i])->sort;
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
    throw IncorrectUsageException("Symbol name " + name
                                  + " has already been used.");
  }

  try
  {
    std::shared_ptr<Cvc5Sort> csort = std::static_pointer_cast<Cvc5Sort>(sort);
    ::cvc5::Term t = instance->tm.mkConst(csort->sort, name);
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
    throw IncorrectUsageException("Symbol named " + name + " does not exist.");
  }
  return it->second;
}

Term Cvc5Solver::make_param(const std::string name, const Sort & sort) const
{
  try
  {
    std::shared_ptr<Cvc5Sort> csort = std::static_pointer_cast<Cvc5Sort>(sort);
    ::cvc5::Term t = instance->tm.mkVar(csort->sort, name);
    return std::make_shared<::smt::Cvc5Term>(t);
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Sort Cvc5Solver::make_sort(const DatatypeDecl & d) const
{
  try
  {
    std::shared_ptr<Cvc5DatatypeDecl> cd =
        std::static_pointer_cast<Cvc5DatatypeDecl>(d);

    return std::make_shared<Cvc5Sort>(
        instance->tm.mkDatatypeSort(cd->datatypedecl));
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
};

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
};

void Cvc5Solver::add_constructor(DatatypeDecl & dt,
                                 const DatatypeConstructorDecl & con) const
{
  try
  {
    std::shared_ptr<Cvc5DatatypeDecl> cdt =
        std::static_pointer_cast<Cvc5DatatypeDecl>(dt);
    std::shared_ptr<Cvc5DatatypeConstructorDecl> ccon =
        std::static_pointer_cast<Cvc5DatatypeConstructorDecl>(con);
    cdt->datatypedecl.addConstructor(ccon->datatypeconstructordecl);
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
};

void Cvc5Solver::add_selector(DatatypeConstructorDecl & dt,
                              const std::string & name,
                              const Sort & s) const
{
  try
  {
    std::shared_ptr<Cvc5DatatypeConstructorDecl> cdt =
        std::static_pointer_cast<Cvc5DatatypeConstructorDecl>(dt);
    std::shared_ptr<Cvc5Sort> cs = std::static_pointer_cast<Cvc5Sort>(s);
    cdt->datatypeconstructordecl.addSelector(name, cs->sort);
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
};

void Cvc5Solver::add_selector_self(DatatypeConstructorDecl & dt,
                                   const std::string & name) const
{
  try
  {
    std::shared_ptr<Cvc5DatatypeConstructorDecl> cdt =
        std::static_pointer_cast<Cvc5DatatypeConstructorDecl>(dt);
    cdt->datatypeconstructordecl.addSelectorSelf(name);
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
};

Term Cvc5Solver::get_constructor(const Sort & s, std::string name) const
{
  try
  {
    std::shared_ptr<Cvc5Sort> cs = std::static_pointer_cast<Cvc5Sort>(s);
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
};

Term Cvc5Solver::get_tester(const Sort & s, std::string name) const
{
  try
  {
    std::shared_ptr<Cvc5Sort> cs = std::static_pointer_cast<Cvc5Sort>(s);
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
};

Term Cvc5Solver::get_selector(const Sort & s,
                              std::string con,
                              std::string name) const
{
  try
  {
    std::shared_ptr<Cvc5Sort> cs = std::static_pointer_cast<Cvc5Sort>(s);
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
};

SortVec Cvc5Solver::make_datatype_sorts(
    const std::vector<DatatypeDecl> & decls) const
{
  try
  {
    SortVec dt_sorts;
    dt_sorts.reserve(decls.size());

    std::vector<cvc5::DatatypeDecl> cvc5_decls;
    cvc5_decls.reserve(decls.size());
    for (const auto & d : decls)
    {
      cvc5_decls.push_back(
          std::static_pointer_cast<Cvc5DatatypeDecl>(d)->datatypedecl);
    }

    for (const auto & csort : instance->tm.mkDatatypeSorts(cvc5_decls))
    {
      dt_sorts.push_back(std::make_shared<Cvc5Sort>(csort));
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
                                  + " to zero terms.");
  }
  else if (op.prim_op == Forall || op.prim_op == Exists)
  {
    check_quantifier_binders(op, terms);
  }
  else if (terms.size() > 2
           && binary_only_ops.find(op.prim_op) != binary_only_ops.end())
  {
    return make_nary_term(this, op, terms);
  }

  try
  {
    std::vector<::cvc5::Term> cterms;
    cterms.reserve(terms.size());
    std::shared_ptr<Cvc5Term> cterm;
    for (auto t : terms)
    {
      cterm = std::static_pointer_cast<Cvc5Term>(t);
      cterms.push_back(cterm->term);
    }
    if (op.prim_op == Forall || op.prim_op == Exists)
    {
      ::cvc5::Kind quant_kind = primop2kind.at(op.prim_op);
      ::cvc5::Term quant_res = cterms.back();
      cterms.pop_back();
      // bind quantifiers one a time
      // makes traversal easier since smt-switch has no
      // VARIABLE_LIST equivalent
      while (cterms.size())
      {
        ::cvc5::Term bound_var =
            instance->tm.mkTerm(cvc5::Kind::VARIABLE_LIST, { cterms.back() });
        cterms.pop_back();
        quant_res = instance->tm.mkTerm(quant_kind, { bound_var, quant_res });
      }
      return std::make_shared<Cvc5Term>(quant_res);
    }
    else if (op.num_idx == 0)
    {
      return std::make_shared<Cvc5Term>(
          instance->tm.mkTerm(primop2kind.at(op.prim_op), cterms));
    }
    else
    {
      ::cvc5::Op cvc5_op = make_cvc5_op(op);
      return std::make_shared<Cvc5Term>(instance->tm.mkTerm(cvc5_op, cterms));
    }
  }
  catch (::cvc5::CVC5ApiException & e)
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
    keys.push_back(std::static_pointer_cast<Cvc5Term>(elem.first)->term);
    values.push_back(std::static_pointer_cast<Cvc5Term>(elem.second)->term);
  }

  ::cvc5::Term cterm = std::static_pointer_cast<Cvc5Term>(term)->term;
  return std::make_shared<Cvc5Term>(cterm.substitute(keys, values));
}

/**
   Helper function for creating a cvc5 Op from an Op
   Preconditions: op must be indexed, i.e. op.num_idx > 0
*/
::cvc5::Op Cvc5Solver::make_cvc5_op(Op op) const
{
  if (primop2kind.find(op.prim_op) == primop2kind.end())
  {
    throw IncorrectUsageException(
        smt::to_string(op.prim_op)
        + " not recognized as a PrimOp for an indexed operator.");
  }
  if (op.num_idx == 1)
  {
    return instance->tm.mkOp(primop2kind.at(op.prim_op),
                             { narrow_index(op, op.idx0) });
  }
  else if (op.num_idx == 2)
  {
    return instance->tm.mkOp(
        primop2kind.at(op.prim_op),
        { narrow_index(op, op.idx0), narrow_index(op, op.idx1) });
  }
  else
  {
    throw NotImplementedException(
        "cvc5 does not have any indexed "
        "operators with more than two indices");
  }
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

cvc5InterpolatingSolver::cvc5InterpolatingSolver()
    : AbsSmtInterpolator(CVC5_INTERPOLATOR, std::make_shared<Cvc5Solver>()),
      cvc5_solver(std::static_pointer_cast<Cvc5Solver>(backend_solver))
{
  initialize();
}

void cvc5InterpolatingSolver::initialize()
{
  // set_opt refuses produce-interpolants, so this is the only place it is set
  cvc5_solver->set_opt("produce-interpolants", "true");
  // each query is asked between a push and a pop, which need it
  cvc5_solver->set_opt("incremental", "true");
}

// incremental never gets here, so cvc5's own option stays on
void cvc5InterpolatingSolver::do_set_opt(const std::string & option,
                                         const std::string & value)
{
  if (option == "produce-interpolants")
  {
    throw IncorrectUsageException("cvc5 interpolator does not allow option: "
                                  + option);
  }
  cvc5_solver->set_opt(option, value);
}

// cvc5 interpolates between its assertions and a given formula, so A is
// asserted and the interpolant asked for not B
Result cvc5InterpolatingSolver::get_interpolant(const Term & A,
                                                const Term & B,
                                                Term & out_I) const
{
  if (A->get_sort()->get_sort_kind() != BOOL
      || B->get_sort()->get_sort_kind() != BOOL)
  {
    throw IncorrectUsageException("get_interpolant requires boolean terms");
  }

  std::shared_ptr<cvc5::Solver> solver = cvc5_solver->get_cvc5_solver();
  ::cvc5::Term notB =
      std::static_pointer_cast<Cvc5Term>(make_term(Not, B))->term;
  ::cvc5::Term I;
  solver->push();
  try
  {
    solver->assertFormula(std::static_pointer_cast<Cvc5Term>(A)->term);
    I = solver->getInterpolant(notB);
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    solver->pop();
    throw InternalSolverException(e.what());
  }
  solver->pop();
  if (I.isNull())
  {
    return Result(UNKNOWN, "cvc5 found no interpolant");
  }
  out_I = std::make_shared<Cvc5Term>(I);
  return Result(UNSAT);
}

Result cvc5InterpolatingSolver::get_sequence_interpolants(
    const TermVec & formulae, TermVec & out_I) const
{
  return sequence_from_interpolants(formulae, out_I);
}

}  // namespace smt
