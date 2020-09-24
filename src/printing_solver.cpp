/*********************                                                        */
/*! \file printing_solver.cpp
** \verbatim
** Top contributors (to current version):
**   Yoni Zohar
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Class that wraps another SmtSolver and dumps SMT-LIB
**        that corresponds to the operations being performed.
**        The SMT-LIB command is printed before being executed,
**        so that in case of an error it easier to see when it happened.
**/

#include "printing_solver.h"
#include "utils.h"

/* string macros for the SMT-LIB commands */
#define SET_OPTION_STR "set-option"
#define SET_LOGIC_STR "set-logic"
#define DECLARE_FUN_STR "declare-fun"
#define DECLARE_SORT_STR "declare-sort"
#define ASSERT_STR "assert"
#define CHECK_SAT_STR "check-sat"
#define CHECK_SAT_ASSUMING_STR "check-sat-assuming"
#define GET_VALUE_STR "get-value"
#define GET_UNSAT_ASSUMPTIONS_STR "get-unsat-assumptions"
#define PUSH_STR "push"
#define POP_STR "pop"
#define RESET_ASSERTIONS_STR "reset-assertions"
#define RESET_STR "reset"
#define INTERPOLATION_GROUP_STR "interpolation-group"
#define MSAT_GET_INTERPOLANT_STR "get-interpolant"

using namespace std;

namespace smt {

/* PrintingSolver */

// implementations
PrintingSolver::PrintingSolver(SmtSolver s, std::ostream* os, PrintingStyleEnum pse)
    : AbsSmtSolver(s->get_solver_enum()),
      wrapped_solver(s), out_stream(os), style(pse)
{
}

PrintingSolver::~PrintingSolver() {}

Sort PrintingSolver::make_sort(const string name, uint64_t arity) const
{
  (*out_stream) << "(" << DECLARE_SORT_STR << " " << name << " " << arity << ")" << endl;
  return wrapped_solver->make_sort(name, arity);
}

Sort PrintingSolver::make_sort(const SortKind sk) const
{
  return wrapped_solver->make_sort(sk);
}

Sort PrintingSolver::make_sort(const SortKind sk, uint64_t size) const
{
  return wrapped_solver->make_sort(sk, size);
}

Sort PrintingSolver::make_sort(const SortKind sk, const Sort & sort1) const
{
  return wrapped_solver->make_sort(sk, sort1);
}

Sort PrintingSolver::make_sort(const SortKind sk,
                              const Sort & sort1,
                              const Sort & sort2) const
{
  return wrapped_solver->make_sort(sk, sort1, sort2);
}

Sort PrintingSolver::make_sort(const SortKind sk,
                              const Sort & sort1,
                              const Sort & sort2,
                              const Sort & sort3) const
{
  return wrapped_solver->make_sort(sk, sort1, sort2, sort3);
}

Sort PrintingSolver::make_sort(SortKind sk, const SortVec & sorts) const
{
  return wrapped_solver->make_sort(sk, sorts);
}

Sort PrintingSolver::make_sort(const Sort & sort_con,
                               const SortVec & sorts) const
{
  return wrapped_solver->make_sort(sort_con, sorts);
}

Sort PrintingSolver::make_sort(const DatatypeDecl & d) const {
  throw NotImplementedException("PrintingSolver::make_sort");
};
DatatypeDecl PrintingSolver::make_datatype_decl(const std::string & s)  {
    throw NotImplementedException("PrintingSolver::make_datatype_decl");
}
DatatypeConstructorDecl PrintingSolver::make_datatype_constructor_decl(
    const std::string s)
{
  throw NotImplementedException(
      "PrintingSolver::make_datatype_constructor_decl");
};
void PrintingSolver::add_constructor(DatatypeDecl & dt, const DatatypeConstructorDecl & con) const {
  throw NotImplementedException("PrintingSolver::add_constructor");
};
void PrintingSolver::add_selector(DatatypeConstructorDecl & dt, const std::string & name, const Sort & s) const {
  throw NotImplementedException("PrintingSolver::add_selector");
};
void PrintingSolver::add_selector_self(DatatypeConstructorDecl & dt, const std::string & name) const {
  throw NotImplementedException("PrintingSolver::add_selector_self");
};

Term PrintingSolver::get_constructor(const Sort & s, std::string name) const  {
  throw NotImplementedException("PrintingSolver::get_constructor");
};
Term PrintingSolver::get_tester(const Sort & s, std::string name) const  {
  throw NotImplementedException("PrintingSolver::get_testeer");
};

Term PrintingSolver::get_selector(const Sort & s, std::string con, std::string name) const  {
  throw NotImplementedException("PrintingSolver::get_selector");
};


Term PrintingSolver::make_term(bool b) const
{
  return wrapped_solver->make_term(b);
}

Term PrintingSolver::make_term(int64_t i, const Sort & sort) const
{
  return wrapped_solver->make_term(i, sort);
}

Term PrintingSolver::make_term(const string name,
                              const Sort & sort,
                              uint64_t base) const
{
  return wrapped_solver->make_term(name, sort, base);
}

Term PrintingSolver::make_term(const Term & val, const Sort & sort) const
{
  return wrapped_solver->make_term(val, sort);
}

Term PrintingSolver::make_symbol(const string name, const Sort & sort)
{
  SortKind sk = sort->get_sort_kind();
  string domain_str = "";
  string range_str = "";
  if (sk == smt::SortKind::FUNCTION) {
    for (Sort ds : sort->get_domain_sorts()) {
      domain_str += ds->to_string() + " ";
    }
    range_str = sort->get_codomain_sort()->to_string();
  } else {
    range_str = sort->to_string();
  }
  (*out_stream) << "(" << DECLARE_FUN_STR << " " << name << " " << "(" << domain_str << ")" << " " << range_str << ")" << endl;
  return wrapped_solver->make_symbol(name, sort);
}

Term PrintingSolver::make_param(const string name, const Sort & sort)
{
  // bound parameters are not declared -- they'll show up in the printed term
  return wrapped_solver->make_param(name, sort);
}

Term PrintingSolver::make_term(const Op op, const Term & t) const
{
  return wrapped_solver->make_term(op, t);
}

Term PrintingSolver::make_term(const Op op,
                              const Term & t1,
                              const Term & t2) const
{
  return wrapped_solver->make_term(op, t1, t2);
}

Term PrintingSolver::make_term(const Op op,
                              const Term & t1,
                              const Term & t2,
                              const Term & t3) const
{
  return wrapped_solver->make_term(op, t1, t2, t3);
}

Term PrintingSolver::make_term(const Op op, const TermVec & terms) const
{
  return wrapped_solver->make_term(op, terms);
}

Term PrintingSolver::get_value(const Term & t) const
{
  (*out_stream) << "(" << GET_VALUE_STR << " (" << t << "))" << endl;
  return wrapped_solver->get_value(t);
}

void PrintingSolver::get_unsat_core(UnorderedTermSet & out)
{
  (*out_stream) << "(" << GET_UNSAT_ASSUMPTIONS_STR << ")" << endl;
  wrapped_solver->get_unsat_core(out);
}

UnorderedTermMap PrintingSolver::get_array_values(const Term & arr,
                                                 Term & out_const_base) const
{
  (*out_stream) << "(get-value (" << arr << "))" << endl;
  return wrapped_solver->get_array_values(arr, out_const_base);
}

void PrintingSolver::reset()
{
  (*out_stream) << "(" << RESET_STR << ")" << endl;
  wrapped_solver->reset();
}

// dispatched to underlying solver

void PrintingSolver::set_opt(const std::string option, const std::string value)
{
  wrapped_solver->set_opt(option, value);
  (*out_stream) << "(" <<  SET_OPTION_STR << " :" << option << " " << value << ")" << endl;
}

void PrintingSolver::set_logic(const std::string logic)
{
  (*out_stream) << "(" << SET_LOGIC_STR << " " << logic << ")" << endl;
  wrapped_solver->set_logic(logic);
}

void PrintingSolver::assert_formula(const Term & t)
{
  (*out_stream) << "(" << ASSERT_STR << " " << t->to_string() << ")" << endl;
  wrapped_solver->assert_formula(t);
}

Result PrintingSolver::check_sat() { 
  (*out_stream) << "(" << CHECK_SAT_STR << ")" << endl;
  return wrapped_solver->check_sat(); 

}

Result PrintingSolver::check_sat_assuming(const TermVec & assumptions)
{
  string assumptions_str;
  for (Term a : assumptions) {
    assumptions_str += a->to_string() + " ";
  }
  (*out_stream) << "(" << CHECK_SAT_ASSUMING_STR << " (" << assumptions_str << "))" << endl;
  return wrapped_solver->check_sat_assuming(assumptions);
}

void PrintingSolver::push(uint64_t num) { 
  (*out_stream) << "(" << PUSH_STR << " " << num << ")" << endl;
  wrapped_solver->push(num); 
}

void PrintingSolver::pop(uint64_t num) { 
  (*out_stream) << "(" << POP_STR << " " << num << ")" << endl;
  wrapped_solver->pop(num); 
}

void PrintingSolver::reset_assertions() { 
  (*out_stream) << "(" << RESET_ASSERTIONS_STR << ")" << endl;
  wrapped_solver->reset_assertions(); 
}

Result PrintingSolver::get_interpolant(const Term & A,
                                       const Term & B,
                                       Term & out_I) const
{
  /* currently we only support printing msat interpolation commands.
   * The printing follows the internal implementation from msat_solver.h
   * in which the assertions are labeled by interpolation groups
   */
  assert(style == PrintingStyleEnum::MSAT_STYLE);
  (*out_stream) << "(" << ASSERT_STR << " (! " << A << " :" << INTERPOLATION_GROUP_STR << " g1))" << endl;
  (*out_stream) << "(" << ASSERT_STR << " (! " << B << " :" << INTERPOLATION_GROUP_STR << " g2))" << endl;;
  (*out_stream) << "(" << CHECK_SAT_STR << ")" << endl;
  (*out_stream) << "(" << MSAT_GET_INTERPOLANT_STR << " (g1)" << ")" << endl;
  (*out_stream) << "; when running mathsat, use `-interpolation=true` flag" << endl;
  return wrapped_solver->get_interpolant(A, B, out_I);
}

SmtSolver create_printing_solver(SmtSolver wrapped_solver, std::ostream* out_stream, PrintingStyleEnum style) {
  return std::make_shared<PrintingSolver>(wrapped_solver, out_stream, style);

}

}  // namespace smt
