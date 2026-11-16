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

#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <list>
#include <memory>
#include <stdexcept>
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
#include "smt-switch/term_visitor.h"
#include "smt-switch/utils.h"

namespace smt {

// TODO: Implement a generic visitor

AbsSmtSolver::AbsSmtSolver(SolverEnum se) : solver_enum(se) {}

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
                                + to_string(solver_enum));
}

Term AbsSmtSolver::make_term(const std::wstring & /* s */,
                             const Sort & /* sort */) const
{
  throw NotImplementedException("Strings are not supported by "
                                + to_string(solver_enum));
}

Sort AbsSmtSolver::make_sort(const DatatypeDecl & /* d */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(solver_enum));
}

DatatypeDecl AbsSmtSolver::make_datatype_decl(const std::string & /* s */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(solver_enum));
}

DatatypeConstructorDecl AbsSmtSolver::make_datatype_constructor_decl(
    const std::string /* s */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(solver_enum));
}

void AbsSmtSolver::add_constructor(
    DatatypeDecl & /* dt */, const DatatypeConstructorDecl & /* con */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(solver_enum));
}

void AbsSmtSolver::add_selector(DatatypeConstructorDecl & /* dt */,
                                const std::string & /* name */,
                                const Sort & /* s */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(solver_enum));
}

void AbsSmtSolver::add_selector_self(DatatypeConstructorDecl & /* dt */,
                                     const std::string & /* name */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(solver_enum));
}

Term AbsSmtSolver::get_constructor(const Sort & /* s */,
                                   std::string /* name */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(solver_enum));
}

Term AbsSmtSolver::get_tester(const Sort & /* s */,
                              std::string /* name */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(solver_enum));
}

Term AbsSmtSolver::get_selector(const Sort & /* s */,
                                std::string /* con */,
                                std::string /* name */) const
{
  throw NotImplementedException("Datatypes are not supported by "
                                + to_string(solver_enum));
}

SortVec AbsSmtSolver::make_datatype_sorts(
    const std::vector<DatatypeDecl> & /* decls */) const
{
  throw NotImplementedException("make_datatype_sorts is not implemented by "
                                + to_string(solver_enum));
}

Sort AbsSmtSolver::make_datatype_sort(const DatatypeDecl & decl) const
{
  SortVec datatype_sorts = make_datatype_sorts({ decl });
  if (datatype_sorts.size() != 1)
  {
    throw SolverException("make_datatype_sorts gave "
                          + std::to_string(datatype_sorts.size())
                          + " sorts for one datatype declaration");
  }
  return datatype_sorts[0];
}

Term AbsSmtSolver::substitute(const Term term,
                              const UnorderedTermMap & substitution_map) const
{
  // each term's result once it is known; a term is rebuilt the second time
  // it comes off the stack, after its children
  UnorderedTermMap cache;
  UnorderedTermSet visited;
  TermVec to_visit{ term };
  TermVec cached_children;
  Term t;
  while (to_visit.size())
  {
    t = to_visit.back();
    to_visit.pop_back();
    if (cache.find(t) != cache.end())
    {
      continue;
    }
    // a key is replaced whole, whatever it is made of
    auto it = substitution_map.find(t);
    if (it != substitution_map.end())
    {
      cache[t] = it->second;
      continue;
    }
    if (visited.insert(t).second)
    {
      to_visit.push_back(t);
      for (auto c : t)
      {
        to_visit.push_back(c);
      }
      continue;
    }
    cached_children.clear();
    for (auto c : t)
    {
      cached_children.push_back(cache.at(c));
    }

    // const arrays have children but don't need to be rebuilt
    // (they're constructed in a particular way anyway)
    cache[t] = cached_children.size() && !t->is_value()
                   ? make_term(t->get_op(), cached_children)
                   : t;
  }

  return cache.at(term);
}

TermVec AbsSmtSolver::substitute_terms(
    const TermVec & terms, const UnorderedTermMap & substitution_map) const
{
  TermVec res;
  res.reserve(terms.size());
  for (auto t : terms)
  {
    res.push_back(substitute(t, substitution_map));
  }
  return res;
}

void AbsSmtSolver::dump_smt2(std::string /* filename */) const
{
  throw NotImplementedException("Dumping to a file is not supported by "
                                + to_string(solver_enum));
}

SolverEnum AbsSmtSolver::get_solver_enum() const { return solver_enum; }

Term AbsSmtSolver::make_nary_term(const Op & op, const TermVec & terms) const
{
  std::size_t size = terms.size();
  if (size < 2)
  {
    throw IncorrectUsageException("Can't apply " + op.to_string() + " to "
                                  + std::to_string(size) + " terms.");
  }
  if (is_left_assoc(op.prim_op))
  {
    Term res = terms[0];
    for (std::size_t i = 1; i < size; ++i)
    {
      res = make_term(op, res, terms[i]);
    }
    return res;
  }
  else if (is_right_assoc(op.prim_op))
  {
    Term res = terms[size - 1];
    for (std::size_t i = 1; i < size; ++i)
    {
      res = make_term(op, terms[size - 1 - i], res);
    }
    return res;
  }

  TermVec conjuncts;
  if (is_chainable(op.prim_op))
  {
    for (std::size_t i = 0; i + 1 < size; ++i)
    {
      conjuncts.push_back(make_term(op, terms[i], terms[i + 1]));
    }
  }
  else if (is_pairwise(op.prim_op))
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
  return conjuncts.size() == 1 ? conjuncts[0] : make_term(And, conjuncts);
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

bool AbsSmtSolver::parse_bool_opt(const std::string & option,
                                  const std::string & value)
{
  if (value != "true" && value != "false")
  {
    throw IncorrectUsageException("The option " + option
                                  + " takes true or false, not " + value);
  }
  return value == "true";
}

std::chrono::duration<double> AbsSmtSolver::parse_time_limit(
    const std::string & value)
{
  double seconds = 0;
  std::size_t end = 0;
  try
  {
    seconds = std::stod(value, &end);
  }
  catch (const std::logic_error &)
  {
    // std::stod failed, so end is still zero
  }
  if (end == 0 || end != value.size() || !std::isfinite(seconds) || seconds < 0)
  {
    throw IncorrectUsageException(
        "The option time-limit takes a nonnegative number of seconds, not "
        + value);
  }
  // Half of what a clock counting nanoseconds in 64 bits holds, so that a
  // solver adding the limit to the time now cannot overflow; a longer limit
  // is as good as none.
  constexpr double longest =
      std::chrono::duration<double>(std::chrono::nanoseconds::max()).count()
      / 2;
  return std::chrono::duration<double>(std::min(seconds, longest));
}

// parse_nat_opt, arith_value_to_decimal, bv_value_to_bits, bv_value_to_words
// and bv_value_to_uint64 are defined in numeral_utils.cpp, beside the
// smtlib:: parsers they share helpers with.

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

namespace {

// Collects the theory atoms of a formula, going through its connectives.
// With split_ites, an application with if-then-else children is visited
// once for each choice of their branches, and their conditions too.
class TheoryAtomsVisitor : public TermVisitor
{
 public:
  TheoryAtomsVisitor(std::shared_ptr<const AbsSmtSolver> solver,
                     bool split_ites,
                     UnorderedTermSet & out)
      : solver_(solver),
        boolsort_(solver->make_sort(BOOL)),
        split_ites_(split_ites),
        out_(out)
  {
  }

 protected:
  VisitResult visit_term(const Term & term) override
  {
    if (term->get_sort() != boolsort_ || term->is_value())
    {
      return VisitResult::Skip;
    }
    if (split_ites_)
    {
      // each child's choices: both branches of an if-then-else, else itself
      std::vector<TermVec> choices;
      bool has_ite = false;
      for (const Term & c : term)
      {
        if (c->get_op() == Ite)
        {
          has_ite = true;
          TermVec ite(c->begin(), c->end());
          visit(ite[0]);
          choices.push_back({ ite[1], ite[2] });
        }
        else
        {
          choices.push_back({ c });
        }
      }
      if (has_ite)
      {
        // count through every combination of choices, the first fastest
        std::vector<std::size_t> picks(choices.size(), 0);
        std::size_t i = 0;
        while (i < picks.size())
        {
          TermVec children;
          for (std::size_t j = 0; j < choices.size(); ++j)
          {
            children.push_back(choices[j][picks[j]]);
          }
          visit(solver_->make_term(term->get_op(), children));
          for (i = 0; i < picks.size() && ++picks[i] == choices[i].size(); ++i)
          {
            picks[i] = 0;
          }
        }
        return VisitResult::Continue;
      }
    }
    if (is_theory_atom(term, boolsort_))
    {
      out_.insert(term);
      return VisitResult::Skip;
    }
    return VisitResult::Continue;
  }

 private:
  std::shared_ptr<const AbsSmtSolver> solver_;
  Sort boolsort_;
  bool split_ites_;
  UnorderedTermSet & out_;
};

// Collects the symbolic constants that fix the values of terms in the
// model, following only the child that decides a term's value when one
// does
class JustificationVisitor : public TermVisitor
{
 public:
  JustificationVisitor(std::shared_ptr<const AbsSmtSolver> solver,
                       UnorderedTermSet & out)
      : solver_(solver), out_(out)
  {
  }

 protected:
  VisitResult visit_term(const Term & term) override
  {
    Op op = term->get_op();
    if (op.is_null())
    {
      if (term->is_symbolic_const())
      {
        out_.insert(term);
      }
      return VisitResult::Skip;
    }
    TermVec children(term->begin(), term->end());
    if (op == Ite)
    {
      visit(children[0]);
      visit(solver_->get_value(children[0])->to_bool() ? children[1]
                                                       : children[2]);
      return VisitResult::Skip;
    }
    Term decider;
    if (op == And || op == Or)
    {
      // a false conjunct or a true disjunct
      bool deciding_value = op == Or;
      for (const Term & c : children)
      {
        if (solver_->get_value(c)->to_bool() == deciding_value)
        {
          decider = c;
          break;
        }
      }
    }
    else if (op == Implies)
    {
      // a false premise, else a true conclusion
      for (std::size_t i = 0; i + 1 < children.size() && !decider; ++i)
      {
        if (!solver_->get_value(children[i])->to_bool())
        {
          decider = children[i];
        }
      }
      if (!decider && solver_->get_value(children.back())->to_bool())
      {
        decider = children.back();
      }
    }
    else if (op == BVAnd || op == BVNand || op == BVMul)
    {
      for (const Term & c : children)
      {
        if (solver_->get_value(c)->to_bits().find('1') == std::string::npos)
        {
          decider = c;
          break;
        }
      }
    }
    else if (op == BVOr || op == BVNor)
    {
      for (const Term & c : children)
      {
        if (solver_->get_value(c)->to_bits().find('0') == std::string::npos)
        {
          decider = c;
          break;
        }
      }
    }
    if (decider)
    {
      visit(decider);
      return VisitResult::Skip;
    }
    return VisitResult::Continue;
  }

 private:
  std::shared_ptr<const AbsSmtSolver> solver_;
  UnorderedTermSet & out_;
};

// boolean ops and the bit-vector ops that mean the same, looked up from
// either side to swap one for the other
constexpr std::pair<PrimOp, PrimOp> bool_bv_ops[] = { { And, BVAnd },
                                                      { Or, BVOr },
                                                      { Xor, BVXor },
                                                      { Not, BVNot },
                                                      { Equal, BVComp } };

/* A value term as another sort */
Term cast_value(const std::shared_ptr<const AbsSmtSolver> & solver,
                const Term & term,
                const Sort & sort)
{
  SortKind sk = sort->get_sort_kind();
  Sort cur_sort = term->get_sort();
  SortKind cur_sk = cur_sort->get_sort_kind();

  if (sk == BOOL && cur_sk == BV)
  {
    if (term->is_value() && cur_sort->get_width() == 1)
    {
      return solver->make_term(term->to_int() == 1);
    }
    throw NotImplementedException("Cannot interpret " + term->to_string()
                                  + " as a bool.");
  }
  else if (sk == BV && cur_sk == BOOL)
  {
    if (sort->get_width() != 1)
    {
      throw NotImplementedException("Cannot interpret " + term->to_string()
                                    + " as " + sort->to_string());
    }

    if (term->is_value())
    {
      return solver->make_term(term->to_bool() ? 1 : 0, sort);
    }
    throw NotImplementedException("Cannot interpret " + term->to_string()
                                  + " as " + sort->to_string());
  }
  else if (sk == REAL && cur_sk == INT)
  {
    return solver->make_term(To_Real, term);
  }
  else if (sk == ARRAY)
  {
    // this is a constant array
    // the only value that has SortKind ARRAY
    // make constant array by recursing on the element value
    return solver->make_term(
        cast_value(solver, *(term->begin()), sort->get_elemsort()), sort);
  }
  else
  {
    throw NotImplementedException("Interpreting " + term->to_string() + " as "
                                  + sort->to_string()
                                  + " is not yet implemented.");
  }
}

}  // namespace

Term AbsSmtSolver::cast_term(const Term & term, const Sort & sort) const
{
  Sort cur_sort = term->get_sort();
  if (cur_sort == sort)
  {
    // nothing to do
    return term;
  }
  else if (term->is_value())
  {
    return cast_value(shared_from_this(), term, sort);
  }

  SortKind sk = sort->get_sort_kind();
  SortKind cur_sk = cur_sort->get_sort_kind();

  if (sk == BV && cur_sk == BOOL)
  {
    return make_term(Ite, term, make_term(1, sort), make_term(0, sort));
  }
  else if (sk == BOOL && cur_sk == BV)
  {
    return make_term(Equal, term, make_term(1, cur_sort));
  }
  else if (sk == INT && cur_sk == REAL)
  {
    return make_term(To_Int, term);
  }
  else if (sk == REAL && cur_sk == INT)
  {
    return make_term(To_Real, term);
  }
  else
  {
    throw NotImplementedException("Cannot interpret " + term->to_string()
                                  + " as " + sort->to_string());
  }
}

Term AbsSmtSolver::cast_op(const Op & op, const TermVec & terms) const
{
  if (op.check_sortedness(terms))
  {
    return make_term(op, terms);
  }

  PrimOp po = op.prim_op;

  // priority is turning bitvector operations to boolean operations
  // Heuristic, because boolector represents everything with bit-vector
  // operators, the most common scenario is turning bitvector ops to
  // boolean

  const auto * bool_bv_begin = std::begin(bool_bv_ops);
  const auto * bool_bv_end = std::end(bool_bv_ops);
  auto bool_is_po = [po](const auto & ops) { return ops.first == po; };
  auto bv_is_po = [po](const auto & ops) { return ops.second == po; };
  const auto * as_bool = std::find_if(bool_bv_begin, bool_bv_end, bv_is_po);
  const auto * as_bv = std::find_if(bool_bv_begin, bool_bv_end, bool_is_po);

  // case 1 -- bitvector to boolean op
  if (as_bool != bool_bv_end)
  {
    TermVec casted_children;
    casted_children.reserve(terms.size());
    Sort boolsort = make_sort(BOOL);
    for (auto t : terms)
    {
      casted_children.push_back(cast_term(t, boolsort));
    }
    return make_term(as_bool->first, casted_children);
  }
  // case 2 -- boolean to bitvector op
  else if (as_bv != bool_bv_end)
  {
    TermVec casted_children;
    casted_children.reserve(terms.size());
    Sort bv1sort = make_sort(BV, 1);
    for (auto t : terms)
    {
      casted_children.push_back(cast_term(t, bv1sort));
    }
    return make_term(as_bv->second, casted_children);
  }
  // case 3 -- cast all bit-vectors to booleans
  // a boolean operator that can't be converted to a bit-vector operator easily
  // (easily meaning by just switching the PrimOp)
  else if (po == Implies)
  {
    TermVec casted_children;
    casted_children.reserve(terms.size());
    Sort boolsort = make_sort(BOOL);
    for (auto t : terms)
    {
      casted_children.push_back(cast_term(t, boolsort));
    }
    return make_term(po, casted_children);
  }
  // case 4 -- cast all booleans to bitvectors
  else if (get_theory(po) == Theory::BITVECTORS)
  {
    TermVec casted_children;
    casted_children.reserve(terms.size());
    Sort bv1sort = make_sort(BV, 1);
    for (auto t : terms)
    {
      if (t->get_sort()->get_sort_kind() == BOOL)
      {
        casted_children.push_back(cast_term(t, bv1sort));
      }
      else
      {
        // expecting a bit-vector
        casted_children.push_back(t);
      }
    }
    return make_term(op, casted_children);
  }
  // case 5 -- special case for Ite
  else if (po == Ite)
  {
    Sort boolsort = make_sort(BOOL);
    Term cond = cast_term(terms[0], boolsort);

    Term ifbranch = terms[1];
    Term elsebranch = terms[2];

    SortKind ifsk = ifbranch->get_sort()->get_sort_kind();
    SortKind elsesk = elsebranch->get_sort()->get_sort_kind();
    if (ifsk == INT && elsesk == REAL)
    {
      // MathSAT and Yices2 make an integer-valued Real an Int, so an Ite
      // over Reals can have one branch of each; widen rather than truncate
      ifbranch = cast_term(ifbranch, elsebranch->get_sort());
    }
    else if (ifbranch->get_sort() != elsebranch->get_sort())
    {
      // arbitrarily deciding to cast to the ifbranch sort
      elsebranch = cast_term(elsebranch, ifbranch->get_sort());
    }

    return make_term(Ite, cond, ifbranch, elsebranch);
  }
  // case 7 -- special case for ARRAY select
  else if (po == Select)
  {
    // assuming the array itself doesn't need to be casted
    // only the index
    // we have no support for or issue with that
    return make_term(
        Select,
        terms[0],
        cast_term(terms[1], terms[0]->get_sort()->get_indexsort()));
  }
  // case 8 -- special case for ARRAY store
  else if (po == Store)
  {
    // assuming the array itself doesn't need to be casted
    // only the index
    // we have no support for or issue with that
    Sort arrsort = terms[0]->get_sort();
    return make_term(Store,
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
    if (terms.size() != domain_sorts.size() + 1)
    {
      throw IncorrectUsageException("Can't apply " + terms[0]->to_string()
                                    + " of sort " + funsort->to_string()
                                    + " to " + std::to_string(terms.size() - 1)
                                    + " arguments");
    }
    for (size_t i = 1; i < terms.size(); ++i)
    {
      casted_children.push_back(cast_term(terms[i], domain_sorts[i - 1]));
    }
    return make_term(Apply, casted_children);
  }
  // case 10 -- a quantifier, whose body is a bit-vector of width one in a
  // solver that aliases the two
  else if (po == Forall || po == Exists)
  {
    TermVec casted_children(terms.begin(), terms.end() - 1);
    casted_children.push_back(cast_term(terms.back(), make_sort(BOOL)));
    return make_term(op, casted_children);
  }
  // default case
  else
  {
    std::string msg("Cannot cast this operation: (");
    msg += op.to_string();
    for (auto t : terms)
    {
      msg += " " + t->to_string();
    }
    msg += ")";
    throw NotImplementedException(msg);
  }
}

void AbsSmtSolver::get_theory_atoms(const Term & formula,
                                    UnorderedTermSet & out,
                                    bool split_ites) const
{
  TheoryAtomsVisitor(shared_from_this(), split_ites, out).visit(formula);
}

void AbsSmtSolver::get_justifying_symbols(const Term & term,
                                          UnorderedTermSet & out) const
{
  JustificationVisitor(shared_from_this(), out).visit(term);
}

}  // namespace smt
