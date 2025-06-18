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

#include <cstdint>
#include <limits>
#include <string>

#include "smt.h"
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

/* Cvc5Solver implementation */

Cvc5Solver::Cvc5Solver()
    : AbsSmtSolver(CVC5),
      term_manager(new ::cvc5::TermManager()),
      solver(*term_manager)
{
  solver.setOption("lang", "smt2");
  solver.setOption("bv-print-consts-as-indexed-symbols", "true");
  solver.setOption("arrays-exp", "true");
}

void Cvc5Solver::set_opt(const std::string option, const std::string value)
{
  std::string cvc5option = option;
  std::string cvc5value = value;
  if (option == "time-limit")
  {
    cvc5option = "tlimit-per";
    // convert to milliseconds
    cvc5value = std::to_string(stoi(value) * 1000);
  }

  try
  {
    solver.setOption(cvc5option, cvc5value);
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

void Cvc5Solver::set_logic(const std::string logic)
{
  try
  {
    solver.setLogic(logic);
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term Cvc5Solver::make_term(bool b) const
{
  try
  {
    return std::make_shared<Cvc5Term>(term_manager->mkBoolean(b));
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
      c = term_manager->mkInteger(i);
    }
    else if (sk == REAL)
    {
      c = term_manager->mkReal(i);
    }
    else if (sk == BV)
    {
      // cvc5 uses unsigned integers for mkBitVector
      // to avoid casting issues, always use a string in base 10
      std::string sval = std::to_string(i);
      c = term_manager->mkBitVector(sort->get_width(), sval, 10);
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
      c = term_manager->mkString(s, useEscSequences);
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
      c = term_manager->mkString(s);
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
        c = term_manager->mkInteger(val);
      }
      else
      {
        c = term_manager->mkReal(val);
      }
    }
    else if (sk == BV)
    {
      c = term_manager->mkBitVector(sort->get_width(), val, base);
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
  ::cvc5::Term const_arr = term_manager->mkConstArray(csort->sort, cterm->term);
  return std::make_shared<Cvc5Term>(const_arr);
}

void Cvc5Solver::assert_formula(const Term & t)
{
  try
  {
    std::shared_ptr<Cvc5Term> cterm = std::static_pointer_cast<Cvc5Term>(t);
    solver.assertFormula(cterm->term);
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
    ::cvc5::Result r = solver.checkSat();
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

    std::shared_ptr<Cvc5Term> cterm;
    for (auto a : assumptions)
    {
      cvc5assumps.push_back(std::static_pointer_cast<Cvc5Term>(a)->term);
    }
    return check_sat_assuming(cvc5assumps);
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Result Cvc5Solver::check_sat_assuming_list(const TermList & assumptions)
{
  try
  {
    std::vector<::cvc5::Term> cvc5assumps;
    cvc5assumps.reserve(assumptions.size());

    std::shared_ptr<Cvc5Term> cterm;
    for (auto a : assumptions)
    {
      cvc5assumps.push_back(std::static_pointer_cast<Cvc5Term>(a)->term);
    }
    return check_sat_assuming(cvc5assumps);
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Result Cvc5Solver::check_sat_assuming_set(const UnorderedTermSet & assumptions)
{
  try
  {
    std::vector<::cvc5::Term> cvc5assumps;
    cvc5assumps.reserve(assumptions.size());

    std::shared_ptr<Cvc5Term> cterm;
    for (auto a : assumptions)
    {
      cvc5assumps.push_back(std::static_pointer_cast<Cvc5Term>(a)->term);
    }
    return check_sat_assuming(cvc5assumps);
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

void Cvc5Solver::push(uint64_t num)
{
  try
  {
    solver.push(num);
    context_level += num;
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

void Cvc5Solver::pop(uint64_t num)
{
  try
  {
    solver.pop(num);
    context_level -= num;
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

uint64_t Cvc5Solver::get_context_level() const { return context_level; }

Term Cvc5Solver::get_value(const Term & t) const
{
  try
  {
    std::shared_ptr<Cvc5Term> cterm = std::static_pointer_cast<Cvc5Term>(t);
    return std::make_shared<Cvc5Term>(solver.getValue(cterm->term));
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
    UnorderedTermMap assignments;
    out_const_base = nullptr;
    cvc5::Term carr = std::static_pointer_cast<Cvc5Term>(arr)->term;
    // get the array value
    // cvc5 returns a sequence of stores
    carr = solver.getValue(carr);

    TermVec indices;
    TermVec values;
    Term idx;
    Term val;
    while (carr.hasOp() && carr.getKind() == cvc5::Kind::STORE)
    {
      idx = Term(new Cvc5Term(carr[1]));
      val = Term(new Cvc5Term(carr[2]));
      indices.push_back(idx);
      values.push_back(val);
      carr = carr[0];
    }

    if (carr.getKind() == cvc5::Kind::CONST_ARRAY)
    {
      out_const_base = Term(new Cvc5Term(carr.getConstArrayBase()));
    }

    // now populate the map in reverse order
    Assert(indices.size() == values.size());

    while (indices.size())
    {
      assignments[indices.back()] = values.back();
      indices.pop_back();
      values.pop_back();
    }

    return assignments;
  }
  catch (cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

void Cvc5Solver::get_unsat_assumptions(UnorderedTermSet & out)
{
  Term f;
  try
  {
    for (auto cterm : solver.getUnsatAssumptions())
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
    return std::make_shared<Cvc5Sort>(solver.declareSort(name, arity));
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
      return std::make_shared<Cvc5Sort>(term_manager->getBooleanSort());
    }
    else if (sk == INT)
    {
      return std::make_shared<Cvc5Sort>(term_manager->getIntegerSort());
    }
    else if (sk == REAL)
    {
      return std::make_shared<Cvc5Sort>(term_manager->getRealSort());
    }
    else if (sk == STRING)
    {
      return std::make_shared<Cvc5Sort>(term_manager->getStringSort());
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
      return std::make_shared<Cvc5Sort>(term_manager->mkBitVectorSort(size));
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

Sort Cvc5Solver::make_sort(SortKind sk, const Sort & sort1) const
{
  throw NotImplementedException(
      "Smt-switch does not have any sorts that take one sort parameter yet.");
}

Sort Cvc5Solver::make_sort(SortKind sk,
                           const Sort & sort1,
                           const Sort & sort2) const
{
  try
  {
    if (sk == ARRAY)
    {
      std::shared_ptr<Cvc5Sort> cidxsort =
          std::static_pointer_cast<Cvc5Sort>(sort1);
      std::shared_ptr<Cvc5Sort> celemsort =
          std::static_pointer_cast<Cvc5Sort>(sort2);
      return std::make_shared<Cvc5Sort>(
          term_manager->mkArraySort(cidxsort->sort, celemsort->sort));
    }
    else
    {
      std::string msg("Can't create sort with sort constructor ");
      msg += to_string(sk);
      msg += " and two Sort arguments";
      throw IncorrectUsageException(msg.c_str());
    }
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Sort Cvc5Solver::make_sort(SortKind sk,
                           const Sort & sort1,
                           const Sort & sort2,
                           const Sort & sort3) const
{
  throw NotImplementedException(
      "Smt-switch does not have any sorts that take three sort parameters "
      "yet.");
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
      ::cvc5::Sort cfunsort = term_manager->mkFunctionSort(csorts, csort);
      return std::make_shared<Cvc5Sort>(cfunsort);
    }
    else if (sorts.size() == 1)
    {
      return make_sort(sk, sorts[0]);
    }
    else if (sorts.size() == 2)
    {
      return make_sort(sk, sorts[0], sorts[1]);
    }
    else if (sorts.size() == 3)
    {
      return make_sort(sk, sorts[0], sorts[1], sorts[2]);
    }
    else
    {
      std::string msg("Can't create sort from sort constructor ");
      msg += to_string(sk);
      msg += " with a vector of sorts";
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
    ::cvc5::Term t = term_manager->mkConst(csort->sort, name);
    Term res = std::make_shared<::smt::Cvc5Term>(t);
    symbol_table[name] = res;
    return res;
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term Cvc5Solver::get_symbol(const std::string & name)
{
  auto it = symbol_table.find(name);
  if (it == symbol_table.end())
  {
    throw IncorrectUsageException("Symbol named " + name + " does not exist.");
  }
  return it->second;
}

Term Cvc5Solver::make_param(const std::string name, const Sort & sort)
{
  try
  {
    std::shared_ptr<Cvc5Sort> csort = std::static_pointer_cast<Cvc5Sort>(sort);
    ::cvc5::Term t = term_manager->mkVar(csort->sort, name);
    return std::make_shared<::smt::Cvc5Term>(t);
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term Cvc5Solver::make_term(Op op, const Term & t) const
{
  return make_term(op, TermVec({ t }));
}

Sort Cvc5Solver::make_sort(const DatatypeDecl & d) const
{
  try
  {
    std::shared_ptr<Cvc5DatatypeDecl> cd =
        std::static_pointer_cast<Cvc5DatatypeDecl>(d);

    return std::make_shared<Cvc5Sort>(
        term_manager->mkDatatypeSort(cd->datatypedecl));
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
};

DatatypeDecl Cvc5Solver::make_datatype_decl(const std::string & s)
{
  try
  {
    return std::make_shared<Cvc5DatatypeDecl>(term_manager->mkDatatypeDecl(s));
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

DatatypeConstructorDecl Cvc5Solver::make_datatype_constructor_decl(
    const std::string s)
{
  try
  {
    return std::make_shared<Cvc5DatatypeConstructorDecl>(
        term_manager->mkDatatypeConstructorDecl(s));
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
    cvc5::Datatype dt = cs->sort.getDatatype();
    return std::make_shared<Cvc5Term>(dt.getConstructor(name).getTerm());
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
    cvc5::Datatype dt = cs->sort.getDatatype();
    for (int i = 0; i != dt.getNumConstructors(); i++)
    {
      cvc5::DatatypeConstructor ct = dt[i];
      if (ct.getName() == name)
      {
        return std::make_shared<Cvc5Term>(ct.getTesterTerm());
      }
    }
    throw InternalSolverException(name + " not found in "
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
    cvc5::Datatype dt = cs->sort.getDatatype();
    return std::make_shared<Cvc5Term>(dt.getSelector(name).getTerm());
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

    for (const auto & csort : term_manager->mkDatatypeSorts(cvc5_decls))
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

Term Cvc5Solver::make_term(Op op, const Term & t0, const Term & t1) const
{
  return make_term(op, TermVec({ t0, t1 }));
}

Term Cvc5Solver::make_term(Op op,
                           const Term & t0,
                           const Term & t1,
                           const Term & t2) const
{
  return make_term(op, TermVec({ t0, t1, t2 }));
}

Term Cvc5Solver::make_term(Op op, const TermVec & terms) const
{
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
            term_manager->mkTerm(cvc5::Kind::VARIABLE_LIST, { cterms.back() });
        cterms.pop_back();
        quant_res = term_manager->mkTerm(quant_kind, { bound_var, quant_res });
      }
      return std::make_shared<Cvc5Term>(quant_res);
    }
    else if (op.num_idx == 0)
    {
      return std::make_shared<Cvc5Term>(
          term_manager->mkTerm(primop2kind.at(op.prim_op), cterms));
    }
    else
    {
      ::cvc5::Op cvc5_op = make_cvc5_op(op);
      return std::make_shared<Cvc5Term>(term_manager->mkTerm(cvc5_op, cterms));
    }
  }
  catch (::cvc5::CVC5ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

void Cvc5Solver::reset()
{
  throw NotImplementedException("cvc5 does not support reset");
}

void Cvc5Solver::reset_assertions()
{
  try
  {
    solver.resetAssertions();
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

void Cvc5Solver::dump_smt2(std::string filename) const
{
  throw NotImplementedException("Not yet implemented dumping smt2");
}

/**
   Helper function for creating a cvc5 Op from an Op
   Preconditions: op must be indexed, i.e. op.num_idx > 0
*/
::cvc5::Op Cvc5Solver::make_cvc5_op(Op op) const
{
  if (op.num_idx < 0 || primop2kind.find(op.prim_op) == primop2kind.end())
  {
    throw IncorrectUsageException(
        smt::to_string(op.prim_op)
        + " not recognized as a PrimOp for an indexed operator.");
  }
  if (op.num_idx == 1)
  {
    if (op.idx0 > std::numeric_limits<uint32_t>::max())
    {
      throw SmtException("Op index (" + std::to_string(op.idx0)
                         + ") is too large for cvc5 backend.");
    }
    return term_manager->mkOp(primop2kind.at(op.prim_op),
                              { static_cast<uint32_t>(op.idx0) });
  }
  else if (op.num_idx == 2)
  {
    if (op.idx0 > std::numeric_limits<uint32_t>::max())
    {
      throw SmtException("Op index 0 (" + std::to_string(op.idx0)
                         + ") is too large for cvc5 backend.");
    }
    if (op.idx1 > std::numeric_limits<uint32_t>::max())
    {
      throw SmtException("Op index 1 (" + std::to_string(op.idx1)
                         + ") is too large for cvc5 backend.");
    }
    return term_manager->mkOp(
        primop2kind.at(op.prim_op),
        { static_cast<uint32_t>(op.idx0), static_cast<uint32_t>(op.idx1) });
  }
  else
  {
    throw NotImplementedException(
        "cvc5 does not have any indexed "
        "operators with more than two indices");
  }
}

::cvc5::Solver & Cvc5Solver::get_cvc5_solver() { return solver; }

Result Cvc5Solver::check_sat_assuming(
    const std::vector<cvc5::Term> & cvc5assumps)
{
  ::cvc5::Result r = solver.checkSatAssuming(cvc5assumps);
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

/* end Cvc5Solver implementation */

Result cvc5InterpolatingSolver::get_interpolant(const Term & A,
                                                const Term & B,
                                                Term & out_I) const
{
  solver.resetAssertions();
  if (A->get_sort()->get_sort_kind() != BOOL
      || B->get_sort()->get_sort_kind() != BOOL)
  {
    throw IncorrectUsageException("get_interpolant requires two boolean terms");
  }
  std::shared_ptr<Cvc5Term> cA = std::static_pointer_cast<Cvc5Term>(A);
  std::shared_ptr<Cvc5Term> cB =
      std::static_pointer_cast<Cvc5Term>(make_term(Not, B));
  solver.assertFormula(cA->term);
  cvc5::Term I = solver.getInterpolant(cB->term);
  if (!I.isNull())
  {
    out_I = Term(new Cvc5Term(I));
    return UNSAT;
  }
  else
  {
    return UNKNOWN;
  }
}

}  // namespace smt
