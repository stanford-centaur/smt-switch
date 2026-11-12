/*!
 * \file printing_solver.cpp
 * \brief Class that wraps another SmtSolver and dumps SMT-LIB that corresponds
 *        to the operations being performed
 * \author Yoni Zohar
 * \author Áron Ricardo Perez-Lopez
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Most commands are printed before they are executed, so that in case of an
 * error it is easier to see where it happened. Option, logic, symbol and
 * datatype declarations are printed only once the wrapped solver has accepted
 * them, so that a refused one is not replayed.
 */
#include "smt-switch/printing_solver.h"

#include <cstddef>
#include <cstdint>
#include <memory>
#include <ostream>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "smt-switch/datatype.h"
#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"
#include "smt-switch/utils.h"

namespace smt {

namespace {

/** A constructor declaration of the wrapped solver */
class PrintingDatatypeConstructorDecl : public AbsDatatypeConstructorDecl
{
 public:
  PrintingDatatypeConstructorDecl(DatatypeConstructorDecl wrapped,
                                  std::string n);
  std::string get_name() const override;
  std::size_t hash() const override;
  bool compare(const DatatypeConstructorDecl & d) const override;
  bool less(const DatatypeConstructorDecl & d) const override;

  DatatypeConstructorDecl wrapped_decl;
  std::string name;
};

/** A datatype declaration of the wrapped solver */
class PrintingDatatypeDecl : public AbsDatatypeDecl
{
 public:
  PrintingDatatypeDecl(DatatypeDecl wrapped, std::string n);
  std::string get_name() const override;

  DatatypeDecl wrapped_decl;
  std::string name;
};

PrintingDatatypeConstructorDecl::PrintingDatatypeConstructorDecl(
    DatatypeConstructorDecl wrapped, std::string n)
    : wrapped_decl(std::move(wrapped)), name(std::move(n))
{
}

std::string PrintingDatatypeConstructorDecl::get_name() const { return name; }

std::size_t PrintingDatatypeConstructorDecl::hash() const
{
  return std::hash<DatatypeConstructorDecl>{}(wrapped_decl);
}

bool PrintingDatatypeConstructorDecl::compare(
    const DatatypeConstructorDecl & d) const
{
  std::shared_ptr<PrintingDatatypeConstructorDecl> other =
      std::dynamic_pointer_cast<PrintingDatatypeConstructorDecl>(d);
  return other && wrapped_decl == other->wrapped_decl;
}

bool PrintingDatatypeConstructorDecl::less(
    const DatatypeConstructorDecl & d) const
{
  return wrapped_decl < backend_pointer_cast<PrintingDatatypeConstructorDecl>(d)
                            ->wrapped_decl;
}

PrintingDatatypeDecl::PrintingDatatypeDecl(DatatypeDecl wrapped, std::string n)
    : wrapped_decl(std::move(wrapped)), name(std::move(n))
{
}

std::string PrintingDatatypeDecl::get_name() const { return name; }

}  // namespace

/* PrintingSolver */

// implementations
PrintingSolver::PrintingSolver(SmtSolver s, std::ostream * os)
    : AbsSmtSolver(s->get_kind()), wrapped_solver(std::move(s)), out_stream(os)
{
}

PrintingSolver::PrintingSolver(SmtSolver s,
                               std::ostream * os,
                               PrintingStyleEnum /* pse */)
    : PrintingSolver(std::move(s), os)
{
}

Term PrintingSolver::get_symbol(const std::string & name) const
{
  return wrapped_solver->get_symbol(name);
}

Sort PrintingSolver::make_sort(const std::string name,
                               std::uint64_t arity) const
{
  (*out_stream) << "(" << DECLARE_SORT_STR << " " << name << " " << arity << ")"
                << std::endl;
  return wrapped_solver->make_sort(name, arity);
}

Sort PrintingSolver::make_sort(const DatatypeDecl & d) const
{
  std::shared_ptr<PrintingDatatypeDecl> pd =
      backend_pointer_cast<PrintingDatatypeDecl>(d);
  Sort res = wrapped_solver->make_sort(pd->wrapped_decl);
  (*out_stream) << smtlib_declare_datatypes({ res }) << std::endl;
  return res;
}

SortVec PrintingSolver::make_datatype_sorts(
    const std::vector<DatatypeDecl> & decls) const
{
  std::vector<DatatypeDecl> wrapped_decls;
  wrapped_decls.reserve(decls.size());
  for (const DatatypeDecl & d : decls)
  {
    wrapped_decls.push_back(
        backend_pointer_cast<PrintingDatatypeDecl>(d)->wrapped_decl);
  }
  SortVec res = wrapped_solver->make_datatype_sorts(wrapped_decls);
  (*out_stream) << smtlib_declare_datatypes(res) << std::endl;
  return res;
}

DatatypeDecl PrintingSolver::make_datatype_decl(const std::string & s) const
{
  return std::make_shared<PrintingDatatypeDecl>(
      wrapped_solver->make_datatype_decl(s), s);
}

DatatypeConstructorDecl PrintingSolver::make_datatype_constructor_decl(
    const std::string s) const
{
  return std::make_shared<PrintingDatatypeConstructorDecl>(
      wrapped_solver->make_datatype_constructor_decl(s), s);
}

void PrintingSolver::add_constructor(DatatypeDecl & dt,
                                     const DatatypeConstructorDecl & con) const
{
  std::shared_ptr<PrintingDatatypeDecl> pdt =
      backend_pointer_cast<PrintingDatatypeDecl>(dt);
  std::shared_ptr<PrintingDatatypeConstructorDecl> pcon =
      backend_pointer_cast<PrintingDatatypeConstructorDecl>(con);
  wrapped_solver->add_constructor(pdt->wrapped_decl, pcon->wrapped_decl);
}

void PrintingSolver::add_selector(DatatypeConstructorDecl & dt,
                                  const std::string & name,
                                  const Sort & s) const
{
  std::shared_ptr<PrintingDatatypeConstructorDecl> pcon =
      backend_pointer_cast<PrintingDatatypeConstructorDecl>(dt);
  wrapped_solver->add_selector(pcon->wrapped_decl, name, s);
}

void PrintingSolver::add_selector_self(DatatypeConstructorDecl & dt,
                                       const std::string & name) const
{
  std::shared_ptr<PrintingDatatypeConstructorDecl> pcon =
      backend_pointer_cast<PrintingDatatypeConstructorDecl>(dt);
  wrapped_solver->add_selector_self(pcon->wrapped_decl, name);
}

Term PrintingSolver::get_constructor(const Sort & s, std::string name) const
{
  return wrapped_solver->get_constructor(s, name);
}

Term PrintingSolver::get_tester(const Sort & s, std::string name) const
{
  return wrapped_solver->get_tester(s, name);
}

Term PrintingSolver::get_selector(const Sort & s,
                                  std::string con,
                                  std::string name) const
{
  return wrapped_solver->get_selector(s, con, name);
}

Sort PrintingSolver::make_sort(const SortKind sk) const
{
  return wrapped_solver->make_sort(sk);
}

Sort PrintingSolver::make_sort(const SortKind sk, std::uint64_t size) const
{
  return wrapped_solver->make_sort(sk, size);
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

Term PrintingSolver::make_term(bool b) const
{
  return wrapped_solver->make_term(b);
}

Term PrintingSolver::make_term(std::int64_t i, const Sort & sort) const
{
  return wrapped_solver->make_term(i, sort);
}

Term PrintingSolver::make_term(const std::string & s,
                               bool useEscSequences,
                               const Sort & sort) const
{
  return wrapped_solver->make_term(s, useEscSequences, sort);
}

Term PrintingSolver::make_term(const std::wstring & s, const Sort & sort) const
{
  return wrapped_solver->make_term(s, sort);
}

Term PrintingSolver::make_term(const std::string name,
                               const Sort & sort,
                               std::uint64_t base) const
{
  return wrapped_solver->make_term(name, sort, base);
}

Term PrintingSolver::make_term(const Term & val, const Sort & sort) const
{
  return wrapped_solver->make_term(val, sort);
}

Term PrintingSolver::make_symbol(const std::string name, const Sort & sort)
{
  Term sym = wrapped_solver->make_symbol(name, sort);
  (*out_stream) << smtlib_declare_fun(sym) << std::endl;
  return sym;
}

Term PrintingSolver::make_param(const std::string name, const Sort & sort) const
{
  // bound parameters are not declared -- they'll show up in the printed term
  return wrapped_solver->make_param(name, sort);
}

Term PrintingSolver::make_term(const Op op, const TermVec & terms) const
{
  return wrapped_solver->make_term(op, terms);
}

Term PrintingSolver::get_value(const Term & t) const
{
  (*out_stream) << "(" << GET_VALUE_STR << " (" << t << "))" << std::endl;
  return wrapped_solver->get_value(t);
}

void PrintingSolver::get_unsat_assumptions(UnorderedTermSet & out) const
{
  (*out_stream) << "(" << GET_UNSAT_ASSUMPTIONS_STR << ")" << std::endl;
  wrapped_solver->get_unsat_assumptions(out);
}

UnorderedTermMap PrintingSolver::get_array_values(const Term & arr,
                                                  Term & out_const_base) const
{
  (*out_stream) << "(get-value (" << arr << "))" << std::endl;
  return wrapped_solver->get_array_values(arr, out_const_base);
}

void PrintingSolver::do_reset()
{
  (*out_stream) << "(" << RESET_STR << ")" << std::endl;
  wrapped_solver->reset();
}

// dispatched to underlying solver

void PrintingSolver::set_opt(const std::string option, const std::string value)
{
  wrapped_solver->set_opt(option, value);
  (*out_stream) << "(" << SET_OPTION_STR << " :" << option << " " << value
                << ")" << std::endl;
}

void PrintingSolver::set_logic(const std::string logic)
{
  // printed once the solver accepts it, so a refused one is not replayed
  wrapped_solver->set_logic(logic);
  (*out_stream) << "(" << SET_LOGIC_STR << " " << logic << ")" << std::endl;
}

void PrintingSolver::do_assert(const Term & t)
{
  (*out_stream) << "(" << ASSERT_STR << " " << t->to_string() << ")"
                << std::endl;
  wrapped_solver->assert_formula(t);
}

Result PrintingSolver::check_sat()
{
  (*out_stream) << "(" << CHECK_SAT_STR << ")" << std::endl;
  return wrapped_solver->check_sat();
}

Result PrintingSolver::do_check_sat_assuming(const TermVec & assumptions)
{
  std::string assumptions_str;
  for (Term a : assumptions)
  {
    assumptions_str += a->to_string() + " ";
  }
  (*out_stream) << "(" << CHECK_SAT_ASSUMING_STR << " (" << assumptions_str
                << "))" << std::endl;
  return wrapped_solver->check_sat_assuming(assumptions);
}

void PrintingSolver::do_push(std::uint64_t num)
{
  (*out_stream) << "(" << PUSH_STR << " " << num << ")" << std::endl;
  wrapped_solver->push(num);
}

void PrintingSolver::do_pop(std::uint64_t num)
{
  (*out_stream) << "(" << POP_STR << " " << num << ")" << std::endl;
  wrapped_solver->pop(num);
}

std::uint64_t PrintingSolver::get_context_level() const
{
  return wrapped_solver->get_context_level();
}

void PrintingSolver::dump_smt2(std::string filename) const
{
  wrapped_solver->dump_smt2(filename);
}

void PrintingSolver::do_reset_assertions()
{
  (*out_stream) << "(" << RESET_ASSERTIONS_STR << ")" << std::endl;
  wrapped_solver->reset_assertions();
}

SmtSolver create_printing_solver(SmtSolver wrapped_solver,
                                 std::ostream * out_stream)
{
  return std::make_shared<PrintingSolver>(std::move(wrapped_solver),
                                          out_stream);
}

SmtSolver create_printing_solver(SmtSolver wrapped_solver,
                                 std::ostream * out_stream,
                                 PrintingStyleEnum /* style */)
{
  return create_printing_solver(std::move(wrapped_solver), out_stream);
}

}  // namespace smt
