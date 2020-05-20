/*********************                                                        */
/*! \file cvc4_solver.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief CVC4 implementation of AbsSmtSolver
**
**
**/

#include "cvc4_solver.h"

#include "utils.h"

namespace smt
{

/* CVC4 Op mappings */
const std::unordered_map<PrimOp, ::CVC4::api::Kind> primop2kind(
    { { And, ::CVC4::api::AND },
      { Or, ::CVC4::api::OR },
      { Xor, ::CVC4::api::XOR },
      { Not, ::CVC4::api::NOT },
      { Implies, ::CVC4::api::IMPLIES },
      { Ite, ::CVC4::api::ITE },
      { Iff, ::CVC4::api::EQUAL },
      { Equal, ::CVC4::api::EQUAL },
      { Distinct, ::CVC4::api::DISTINCT },
      /* Uninterpreted Functions */
      { Apply, ::CVC4::api::APPLY_UF },
      /* Arithmetic Theories */
      { Plus, ::CVC4::api::PLUS },
      { Minus, ::CVC4::api::MINUS },
      { Negate, ::CVC4::api::UMINUS },
      { Mult, ::CVC4::api::MULT },
      { Div, ::CVC4::api::DIVISION },
      { IntDiv, ::CVC4::api::INTS_DIVISION },
      { Lt, ::CVC4::api::LT },
      { Le, ::CVC4::api::LEQ },
      { Gt, ::CVC4::api::GT },
      { Ge, ::CVC4::api::GEQ },
      { Mod, ::CVC4::api::INTS_MODULUS },
      { Abs, ::CVC4::api::ABS },
      { Pow, ::CVC4::api::POW },
      { To_Real, ::CVC4::api::TO_REAL },
      { To_Int, ::CVC4::api::TO_INTEGER },
      { Is_Int, ::CVC4::api::IS_INTEGER },
      /* Fixed Size BitVector Theory */
      { Concat, ::CVC4::api::BITVECTOR_CONCAT },
      // Indexed Op
      { Extract, ::CVC4::api::BITVECTOR_EXTRACT },
      { BVNot, ::CVC4::api::BITVECTOR_NOT },
      { BVNeg, ::CVC4::api::BITVECTOR_NEG },
      { BVAnd, ::CVC4::api::BITVECTOR_AND },
      { BVOr, ::CVC4::api::BITVECTOR_OR },
      { BVXor, ::CVC4::api::BITVECTOR_XOR },
      { BVNand, ::CVC4::api::BITVECTOR_NAND },
      { BVNor, ::CVC4::api::BITVECTOR_NOR },
      { BVXnor, ::CVC4::api::BITVECTOR_XNOR },
      { BVComp, ::CVC4::api::BITVECTOR_COMP },
      { BVAdd, ::CVC4::api::BITVECTOR_PLUS },
      { BVSub, ::CVC4::api::BITVECTOR_SUB },
      { BVMul, ::CVC4::api::BITVECTOR_MULT },
      { BVUdiv, ::CVC4::api::BITVECTOR_UDIV },
      { BVSdiv, ::CVC4::api::BITVECTOR_SDIV },
      { BVUrem, ::CVC4::api::BITVECTOR_UREM },
      { BVSrem, ::CVC4::api::BITVECTOR_SREM },
      { BVSmod, ::CVC4::api::BITVECTOR_SMOD },
      { BVShl, ::CVC4::api::BITVECTOR_SHL },
      { BVAshr, ::CVC4::api::BITVECTOR_ASHR },
      { BVLshr, ::CVC4::api::BITVECTOR_LSHR },
      { BVUlt, ::CVC4::api::BITVECTOR_ULT },
      { BVUle, ::CVC4::api::BITVECTOR_ULE },
      { BVUgt, ::CVC4::api::BITVECTOR_UGT },
      { BVUge, ::CVC4::api::BITVECTOR_UGE },
      { BVSlt, ::CVC4::api::BITVECTOR_SLT },
      { BVSle, ::CVC4::api::BITVECTOR_SLE },
      { BVSgt, ::CVC4::api::BITVECTOR_SGT },
      { BVSge, ::CVC4::api::BITVECTOR_SGE },
      // Indexed Op
      { Zero_Extend, ::CVC4::api::BITVECTOR_ZERO_EXTEND },
      // Indexed Op
      { Sign_Extend, ::CVC4::api::BITVECTOR_SIGN_EXTEND },
      // Indexed Op
      { Repeat, ::CVC4::api::BITVECTOR_REPEAT },
      // Indexed Op
      { Rotate_Left, ::CVC4::api::BITVECTOR_ROTATE_LEFT },
      // Indexed Op
      { Rotate_Right, ::CVC4::api::BITVECTOR_ROTATE_RIGHT },
      // Conversion
      { BV_To_Nat, ::CVC4::api::BITVECTOR_TO_NAT },
      // Indexed Op
      { Int_To_BV, ::CVC4::api::INT_TO_BITVECTOR },
      { Select, ::CVC4::api::SELECT },
      { Store, ::CVC4::api::STORE },
      { Apply_Selector,::CVC4::api::APPLY_SELECTOR},
      { Apply_Tester,::CVC4::api::APPLY_TESTER},
      { Apply_Constructor,::CVC4::api::APPLY_CONSTRUCTOR}  });

/* CVC4Solver implementation */

void CVC4Solver::set_opt(const std::string option, const std::string value)
{
  try
  {
    if (option == "produce-unsat-cores")
    {
      // to be consistent with the smt-switch API, we actually use
      // produce-unsat-assumptions
      solver.setOption("produce-unsat-assumptions", value);
    }
    else
    {
      solver.setOption(option, value);
    }
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

void CVC4Solver::set_logic(const std::string logic)
{
  try
  {
    solver.setLogic(logic);
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term CVC4Solver::make_term(bool b) const
{
  try
  {
    return std::make_shared<CVC4Term> (solver.mkBoolean(b));
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term CVC4Solver::make_term(int64_t i, const Sort & sort) const
{
  try
  {
    SortKind sk = sort->get_sort_kind();
    ::CVC4::api::Term c;

    if ((sk == INT) || (sk == REAL))
    {
      c = solver.mkReal(i);
    }
    else if (sk == BV)
    {
      // CVC4 uses unsigned integers for mkBitVector
      // to avoid casting issues, always use a string in base 10
      std::string sval = std::to_string(i);
      c = solver.mkBitVector(sort->get_width(), sval, 10);
    }
    else
    {
      std::string msg = "Can't create constant with integer for sort ";
      msg += sort->to_string();
      throw IncorrectUsageException(msg.c_str());
    }

    return std::make_shared<CVC4Term> (c);
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    // pretty safe to assume that an error is due to incorrect usage
    throw IncorrectUsageException(e.what());
  }
}

Term CVC4Solver::make_term(std::string val,
                           const Sort & sort,
                           uint64_t base) const
{
  try
  {
    SortKind sk = sort->get_sort_kind();
    ::CVC4::api::Term c;

    if ((sk == INT) || (sk == REAL))
    {
      // TODO: Only do these checks in debug
      if (base != 10)
      {
        throw IncorrectUsageException("Can't use non-decimal base for reals and ints");
      }
      c = solver.mkReal(val);
    }
    else if (sk == BV)
    {
      c = solver.mkBitVector(sort->get_width(), val, base);
    }
    else
    {
      std::string msg = "Can't create constant with integer for sort ";
      msg += sort->to_string();
      throw IncorrectUsageException(msg.c_str());
    }

    return std::make_shared<CVC4Term> (c);
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    // pretty safe to assume that an error is due to incorrect usage
    throw IncorrectUsageException(e.what());
  }
}

Term CVC4Solver::make_term(const Term & val, const Sort & sort) const
{
  std::shared_ptr<CVC4Term> cterm = std::static_pointer_cast<CVC4Term>(val);
  std::shared_ptr<CVC4Sort> csort = std::static_pointer_cast<CVC4Sort>(sort);
  ::CVC4::api::Term const_arr = solver.mkConstArray(csort->sort, cterm->term);
  return std::make_shared<CVC4Term> (const_arr);
}

void CVC4Solver::assert_formula(const Term & t)
{
  try
  {
    std::shared_ptr<CVC4Term> cterm = std::static_pointer_cast<CVC4Term>(t);
    solver.assertFormula(cterm->term);
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Result CVC4Solver::check_sat()
{
  try
  {
    ::CVC4::api::Result r = solver.checkSat();
    if (r.isUnsat())
    {
      return Result(UNSAT);
    }
    else if (r.isSat())
    {
      return Result(SAT);
    }
    else if (r.isSatUnknown())
    {
      return Result(UNKNOWN, r.getUnknownExplanation());
    }
    else
    {
      throw NotImplementedException("Unimplemented result type from CVC4");
    }
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Result CVC4Solver::check_sat_assuming(const TermVec & assumptions)
{
  try
  {
    // expecting (possibly negated) boolean literals
    for (auto a : assumptions)
    {
      if (!a->is_symbolic_const() || a->get_sort()->get_sort_kind() != BOOL)
      {
        if (a->get_op() == Not && (*a->begin())->is_symbolic_const())
        {
          continue;
        }
        else
        {
          throw IncorrectUsageException(
              "Expecting boolean indicator literals but got: "
              + a->to_string());
        }
      }
    }

    std::vector<::CVC4::api::Term> cvc4assumps;
    cvc4assumps.reserve(assumptions.size());

    std::shared_ptr<CVC4Term> cterm;
    for (auto a : assumptions)
    {
      cvc4assumps.push_back(std::static_pointer_cast<CVC4Term>(a)->term);
    }
    ::CVC4::api::Result r = solver.checkSatAssuming(cvc4assumps);
    if (r.isUnsat())
    {
      return Result(UNSAT);
    }
    else if (r.isSat())
    {
      return Result(SAT);
    }
    else if (r.isSatUnknown())
    {
      return Result(UNKNOWN, r.getUnknownExplanation());
    }
    else
    {
      throw NotImplementedException("Unimplemented result type from CVC4");
    }
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

void CVC4Solver::push(uint64_t num)
{
  try
  {
    solver.push(num);
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

void CVC4Solver::pop(uint64_t num)
{
  try
  {
    solver.pop(num);
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term CVC4Solver::get_value(const Term & t) const
{
  try
  {
    std::shared_ptr<CVC4Term> cterm = std::static_pointer_cast<CVC4Term>(t);
    return std::make_shared<CVC4Term> (solver.getValue(cterm->term));
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

UnorderedTermMap CVC4Solver::get_array_values(const Term & arr,
                                              Term & out_const_base) const
{
  try
  {
    UnorderedTermMap assignments;
    out_const_base = nullptr;
    CVC4::api::Term carr = std::static_pointer_cast<CVC4Term>(arr)->term;
    // get the array value
    // CVC4 returns a sequence of stores
    carr = solver.getValue(carr);

    TermVec indices;
    TermVec values;
    Term idx;
    Term val;
    while (carr.hasOp() && carr.getOp() == CVC4::api::STORE)
    {
      idx = Term(new CVC4Term(carr[1]));
      val = Term(new CVC4Term(carr[2]));
      indices.push_back(idx);
      values.push_back(val);
      carr = carr[0];
    }

    // TODO: finish this and remove the false
    if (false && carr.getKind() == CVC4::api::STORE_ALL)
    {
      // TODO: after PR merged, need to use getStoreAllBase()
      out_const_base = Term(new CVC4Term(carr[0]));
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
  catch (CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

TermVec CVC4Solver::get_unsat_core()
{
  TermVec core;
  Term f;
  try
  {
    for (auto cterm : solver.getUnsatAssumptions())
    {
      core.push_back(std::make_shared<CVC4Term>(cterm));
    }
  }
  // this function seems to return a different exception type
  catch (std::exception & e)
  {
    throw InternalSolverException(e.what());
  }
  return core;
}

Sort CVC4Solver::make_sort(const std::string name, uint64_t arity) const
{
  try
  {
    return std::make_shared<CVC4Sort> (solver.declareSort(name, arity));
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Sort CVC4Solver::make_sort(SortKind sk) const
{
  try
  {
    if (sk == BOOL)
    {
      return std::make_shared<CVC4Sort> (solver.getBooleanSort());
    }
    else if (sk == INT)
    {
      return std::make_shared<CVC4Sort> (solver.getIntegerSort());
    }
    else if (sk == REAL)
    {
      return std::make_shared<CVC4Sort> (solver.getRealSort());
    }
    else
    {
      std::string msg("Can't create sort with sort constructor ");
      msg += to_string(sk);
      msg += " and no arguments";
      throw IncorrectUsageException(msg.c_str());
    }
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Sort CVC4Solver::make_sort(SortKind sk, uint64_t size) const
{
  try
  {
    if (sk == BV)
    {
      return std::make_shared<CVC4Sort> (solver.mkBitVectorSort(size));
    }
    else
    {
      std::string msg("Can't create sort with sort constructor ");
      msg += to_string(sk);
      msg += " and an integer argument";
      throw IncorrectUsageException(msg.c_str());
    }
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Sort CVC4Solver::make_sort(SortKind sk, const Sort & sort1) const
{
  throw NotImplementedException(
      "Smt-switch does not have any sorts that take one sort parameter yet.");
}

Sort CVC4Solver::make_sort(SortKind sk,
                           const Sort & sort1,
                           const Sort & sort2) const
{
  try
  {
    if (sk == ARRAY)
    {
      std::shared_ptr<CVC4Sort> cidxsort =
          std::static_pointer_cast<CVC4Sort>(sort1);
      std::shared_ptr<CVC4Sort> celemsort =
          std::static_pointer_cast<CVC4Sort>(sort2);
      return std::make_shared<CVC4Sort>
          (solver.mkArraySort(cidxsort->sort, celemsort->sort));
    }
    else
    {
      std::string msg("Can't create sort with sort constructor ");
      msg += to_string(sk);
      msg += " and two Sort arguments";
      throw IncorrectUsageException(msg.c_str());
    }
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Sort CVC4Solver::make_sort(SortKind sk,
                           const Sort & sort1,
                           const Sort & sort2,
                           const Sort & sort3) const
{
  throw NotImplementedException(
      "Smt-switch does not have any sorts that take three sort parameters "
      "yet.");
}

Sort CVC4Solver::make_sort(SortKind sk, const SortVec & sorts) const
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

      std::vector<::CVC4::api::Sort> csorts;
      csorts.reserve(arity);
      ::CVC4::api::Sort csort;
      for (uint32_t i = 0; i < arity; i++)
      {
        csort = std::static_pointer_cast<CVC4Sort>(sorts[i])->sort;
        csorts.push_back(csort);
      }

      csort = std::static_pointer_cast<CVC4Sort>(sorts.back())->sort;
      ::CVC4::api::Sort cfunsort = solver.mkFunctionSort(csorts, csort);
      return std::make_shared<CVC4Sort> (cfunsort);
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
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term CVC4Solver::make_symbol(const std::string name, const Sort & sort)
{
  // check that name is available
  // to make CVC4 behave the same as other solvers
  if (symbols.find(name) != symbols.end())
  {
    throw IncorrectUsageException("symbol " + name + " has already been used.");
  }

  try
  {
    std::shared_ptr<CVC4Sort> csort = std::static_pointer_cast<CVC4Sort>(sort);
    ::CVC4::api::Term t = solver.mkConst(csort->sort, name);
    Term res = std::make_shared<::smt::CVC4Term> (t);
    symbols[name] = res;
    return res;
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term CVC4Solver::make_term(Op op, const Term & t) const
{
  try
  {
    std::shared_ptr<CVC4Term> cterm = std::static_pointer_cast<CVC4Term>(t);
    if (op.num_idx == 0)
    {
      return std::make_shared<CVC4Term>
          (solver.mkTerm(primop2kind.at(op.prim_op), cterm->term));
    }
    else
    {
      ::CVC4::api::Op cvc4_op = make_cvc4_op(op);
      return std::make_shared<CVC4Term> (solver.mkTerm(cvc4_op, cterm->term));
    }
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Sort CVC4Solver::make_sort(const DatatypeDecl & d) const {
  // corresponds to CVC4::api::Solver::mkDatatypeSort
  try
  {
    std::shared_ptr<CVC4DatatypeDecl> cd = std::static_pointer_cast<CVC4DatatypeDecl>(d);

  return std::make_shared<CVC4Sort> (solver.mkDatatypeSort(cd->datatypedecl));
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
};
DatatypeDecl CVC4Solver::make_datatype_decl(const std::string & s)  {
  //corresponds to CVC4::api::Solver::mkDatatypeDecl()
  try
  {
  return std::make_shared<CVC4DatatypeDecl> (solver.mkDatatypeDecl(s));
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

DatatypeConstructorDecl CVC4Solver::make_datatype_constructor_decl(const std::string s) const {
   // corresponds to CVC4::api::DatatypeConstructorDecl initializer
  try
  {
  return std::make_shared<CVC4DatatypeConstructorDecl> (CVC4::api::DatatypeConstructorDecl(s));
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
};

void CVC4Solver::addConstructor(DatatypeDecl & dt, const DatatypeConstructorDecl & con) const {
  // corresponds to CVC4::api::DatatypeDecl::addConstructor
  try
  {
    std::shared_ptr<CVC4DatatypeDecl> cdt = std::static_pointer_cast<CVC4DatatypeDecl>(dt);
    std::shared_ptr<CVC4DatatypeConstructorDecl> ccon = std::static_pointer_cast<CVC4DatatypeConstructorDecl>(con);
    cdt->datatypedecl.addConstructor(ccon->datatypeconstructordecl);
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
};

void CVC4Solver::addSelector(DatatypeConstructorDecl & dt, const std::string & name, const Sort & s) const {
  // corresponds to CVC4::api::DatatypeConstructorDecl::addSelector
  try
  {
    std::shared_ptr<CVC4DatatypeConstructorDecl> cdt = std::static_pointer_cast<CVC4DatatypeConstructorDecl>(dt);
    std::shared_ptr<CVC4Sort> cs = std::static_pointer_cast<CVC4Sort>(s);
    cdt->datatypeconstructordecl.addSelector(name,cs->sort);
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }

};

void CVC4Solver::addSelectorSelf(DatatypeConstructorDecl & dt, const std::string & name) const {
  // corresponds to CVC4::api::DatatypeConstructorDecl::addSelectorSelf
  try
  {
    std::shared_ptr<CVC4DatatypeConstructorDecl> cdt = std::static_pointer_cast<CVC4DatatypeConstructorDecl>(dt);
    cdt->datatypeconstructordecl.addSelectorSelf(name);
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
};

Term CVC4Solver::get_constructor(const Sort & s, std::string name) const  {
  //corresponds to CVC4::api::DatatypeConstructor::getConstructorTerm
  // The constructor name is globally unique, so we can just search the
  // constructors of the datatype (which can be gotten from the sort)
  try
  {
  std::shared_ptr<CVC4Sort> cs = std::static_pointer_cast<CVC4Sort>(s);
  CVC4::api::Datatype dt = cs->sort.getDatatype();
  for (int i=0; i!=dt.getNumConstructors();i++) {
    CVC4::api::DatatypeConstructor ct=dt[i];
    if (ct.getName()==name){
      return std::make_shared<CVC4Term> (ct.getConstructorTerm());}
  }
  throw InternalSolverException("in CVC4Solver::get_constructor, "+name+" not found in "+cs->sort.toString());
  } catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }

};

Term CVC4Solver::get_tester(const Sort & s, std::string name) const  {
  //corresponds to CVC4::api::DatatypeConstructor::getConstructorTerm
  // The constructor name is globally unique, so we can just search the
  // constructors of the datatype (which can be gotten from the sort)
  try
  {
  std::shared_ptr<CVC4Sort> cs = std::static_pointer_cast<CVC4Sort>(s);
  CVC4::api::Datatype dt = cs->sort.getDatatype();
  for (int i=0; i!=dt.getNumConstructors();i++) {
    CVC4::api::DatatypeConstructor ct=dt[i];
    if (ct.getName() == name){
      return std::make_shared<CVC4Term> (ct.getTesterTerm());}
  }
  throw InternalSolverException("in CVC4Solver::get_constructor, "+name+" not found in "+cs->sort.toString());
  } catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }

};


Term CVC4Solver::get_selector(const Sort & s, std::string con, std::string name) const  {
  //corresponds to CVC4::api::DatatypeConstructor::getSelectorTerm
  try
  {
  std::shared_ptr<CVC4Sort> cs = std::static_pointer_cast<CVC4Sort>(s);
  CVC4::api::Datatype dt = cs->sort.getDatatype();
  for (int i=0; i!=dt.getNumConstructors();i++) {
    CVC4::api::DatatypeConstructor ct=dt[i];
    if (ct.getName() == con){
      return std::make_shared<CVC4Term> (ct.getSelectorTerm(name));}
  }
  throw InternalSolverException("in CVC4Solver::get_constructor, "+name+" not found in "+cs->sort.toString());
  } catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
};
Term CVC4Solver::make_term(Op op, const Term & t0, const Term & t1) const
{
  try
  {
    std::shared_ptr<CVC4Term> cterm0 = std::static_pointer_cast<CVC4Term>(t0);
    std::shared_ptr<CVC4Term> cterm1 = std::static_pointer_cast<CVC4Term>(t1);
    if (op.num_idx == 0)
    {
      return std::make_shared<CVC4Term>
          (solver.mkTerm(primop2kind.at(op.prim_op),
                         cterm0->term,
                         cterm1->term));
    }
  else
    {
      ::CVC4::api::Op cvc4_op = make_cvc4_op(op);
      return std::make_shared<CVC4Term>
          (solver.mkTerm(cvc4_op, cterm0->term, cterm1->term));
    }
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term CVC4Solver::make_term(Op op,
                           const Term & t0,
                           const Term & t1,
                           const Term & t2) const
{
  try
  {
    std::shared_ptr<CVC4Term> cterm0 = std::static_pointer_cast<CVC4Term>(t0);
    std::shared_ptr<CVC4Term> cterm1 = std::static_pointer_cast<CVC4Term>(t1);
    std::shared_ptr<CVC4Term> cterm2 = std::static_pointer_cast<CVC4Term>(t2);
    if (op.num_idx == 0)
    {
      return std::make_shared<CVC4Term>
          (solver.mkTerm(primop2kind.at(op.prim_op),
                         cterm0->term,
                         cterm1->term,
                         cterm2->term));
    }
    else
    {
      ::CVC4::api::Op cvc4_op = make_cvc4_op(op);
      return std::make_shared<CVC4Term>
          (solver.mkTerm(cvc4_op, cterm0->term, cterm1->term, cterm2->term));
    }
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

Term CVC4Solver::make_term(Op op, const TermVec & terms) const
{
  try
  {
    std::vector<::CVC4::api::Term> cterms;
    cterms.reserve(terms.size());
    std::shared_ptr<CVC4Term> cterm;
    for (auto t : terms)
    {
      cterm = std::static_pointer_cast<CVC4Term>(t);
      cterms.push_back(cterm->term);
    }
    if (op.num_idx == 0)
    {
      return std::make_shared<CVC4Term>
          (solver.mkTerm(primop2kind.at(op.prim_op), cterms));
    }
    else
    {
      ::CVC4::api::Op cvc4_op = make_cvc4_op(op);
      return std::make_shared<CVC4Term> (solver.mkTerm(cvc4_op, cterms));
    }
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

void CVC4Solver::reset()
{
  throw NotImplementedException("CVC4 does not support reset");
}

void CVC4Solver::reset_assertions()
{
  try
  {
    solver.resetAssertions();
  }
  catch (::CVC4::api::CVC4ApiException & e)
  {
    throw InternalSolverException(e.what());
  }
}

void CVC4Solver::dump_smt2(std::string filename) const
{
  throw NotImplementedException("Not yet implemented dumping smt2");
}

/**
   Helper function for creating a CVC4 Op from an Op
   Preconditions: op must be indexed, i.e. op.num_idx > 0
*/
::CVC4::api::Op CVC4Solver::make_cvc4_op(Op op) const
{
  if (op.num_idx < 0 || primop2kind.find(op.prim_op) == primop2kind.end())
  {
    throw IncorrectUsageException(
        smt::to_string(op.prim_op)
        + " not recognized as a PrimOp for an indexed operator.");
  }
  if (op.num_idx == 1)
  {
    return solver.mkOp(primop2kind.at(op.prim_op), op.idx0);
  }
  else if (op.num_idx == 2)
  {
    return solver.mkOp(primop2kind.at(op.prim_op), op.idx0, op.idx1);
  }
  else
  {
    throw NotImplementedException(
        "CVC4 does not have any indexed "
        "operators with more than two indices");
  }
}

/* end CVC4Solver implementation */

}
