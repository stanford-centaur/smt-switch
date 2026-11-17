/*!
 * \file term_casts.cpp
 * \brief Casts of terms between Bool and bit-vectors and between Int and Real
 * \author Makai Mann
 * \author Áron Ricardo Perez-Lopez
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * It defines AbsSmtSolver::cast_term and AbsSmtSolver::cast_op.
 */
#include <algorithm>
#include <cstddef>
#include <iterator>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"

namespace smt {

namespace {

// boolean ops and the bit-vector ops that mean the same, looked up from
// either side to swap one for the other
constexpr std::pair<Op::Kind, Op::Kind> bool_bv_ops[] = {
  { Op::And, Op::BVAnd },
  { Op::Or, Op::BVOr },
  { Op::Xor, Op::BVXor },
  { Op::Not, Op::BVNot },
  { Op::Equal, Op::BVComp }
};

/* A value term as another sort */
Term cast_value(const std::shared_ptr<const AbsSmtSolver> & solver,
                const Term & term,
                const Sort & sort)
{
  SortKind sk = sort->get_kind();
  Sort cur_sort = term->get_sort();
  SortKind cur_sk = cur_sort->get_kind();

  if (sk == SortKind::BOOL && cur_sk == SortKind::BV)
  {
    if (term->is_value() && cur_sort->get_width() == 1)
    {
      return solver->make_term(term->to_int() == 1);
    }
    throw NotImplementedException("Cannot interpret " + term->to_string()
                                  + " as a bool.");
  }
  else if (sk == SortKind::BV && cur_sk == SortKind::BOOL)
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
  else if (sk == SortKind::REAL && cur_sk == SortKind::INT)
  {
    return solver->make_term(Op::To_Real, term);
  }
  else if (sk == SortKind::ARRAY)
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

  SortKind sk = sort->get_kind();
  SortKind cur_sk = cur_sort->get_kind();

  if (sk == SortKind::BV && cur_sk == SortKind::BOOL)
  {
    return make_term(Op::Ite, term, make_term(1, sort), make_term(0, sort));
  }
  else if (sk == SortKind::BOOL && cur_sk == SortKind::BV)
  {
    return make_term(Op::Equal, term, make_term(1, cur_sort));
  }
  else if (sk == SortKind::INT && cur_sk == SortKind::REAL)
  {
    return make_term(Op::To_Int, term);
  }
  else if (sk == SortKind::REAL && cur_sk == SortKind::INT)
  {
    return make_term(Op::To_Real, term);
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

  Op::Kind op_kind = op.kind();

  // priority is turning bitvector operations to boolean operations
  // Heuristic, because boolector represents everything with bit-vector
  // operators, the most common scenario is turning bitvector ops to
  // boolean

  const auto * bool_bv_begin = std::begin(bool_bv_ops);
  const auto * bool_bv_end = std::end(bool_bv_ops);
  auto bool_is_po = [op_kind](const auto & ops) {
    return ops.first == op_kind;
  };
  auto bv_is_po = [op_kind](const auto & ops) { return ops.second == op_kind; };
  const auto * as_bool = std::find_if(bool_bv_begin, bool_bv_end, bv_is_po);
  const auto * as_bv = std::find_if(bool_bv_begin, bool_bv_end, bool_is_po);

  // case 1 -- bitvector to boolean op
  if (as_bool != bool_bv_end)
  {
    TermVec casted_children;
    casted_children.reserve(terms.size());
    Sort boolsort = make_sort(SortKind::BOOL);
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
    Sort bv1sort = make_sort(SortKind::BV, 1);
    for (auto t : terms)
    {
      casted_children.push_back(cast_term(t, bv1sort));
    }
    return make_term(as_bv->second, casted_children);
  }
  // case 3 -- cast all bit-vectors to booleans
  // a boolean operator that can't be converted to a bit-vector operator easily
  // (easily meaning by just switching the operator)
  else if (op_kind == Op::Implies)
  {
    TermVec casted_children;
    casted_children.reserve(terms.size());
    Sort boolsort = make_sort(SortKind::BOOL);
    for (auto t : terms)
    {
      casted_children.push_back(cast_term(t, boolsort));
    }
    return make_term(op_kind, casted_children);
  }
  // case 4 -- cast all booleans to bitvectors
  else if (op.theory() == Theory::BITVECTORS)
  {
    TermVec casted_children;
    casted_children.reserve(terms.size());
    Sort bv1sort = make_sort(SortKind::BV, 1);
    for (auto t : terms)
    {
      if (t->get_sort()->get_kind() == SortKind::BOOL)
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
  else if (op_kind == Op::Ite)
  {
    Sort boolsort = make_sort(SortKind::BOOL);
    Term cond = cast_term(terms[0], boolsort);

    Term ifbranch = terms[1];
    Term elsebranch = terms[2];

    SortKind ifsk = ifbranch->get_sort()->get_kind();
    SortKind elsesk = elsebranch->get_sort()->get_kind();
    if (ifsk == SortKind::INT && elsesk == SortKind::REAL)
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

    return make_term(Op::Ite, cond, ifbranch, elsebranch);
  }
  // case 7 -- special case for ARRAY select
  else if (op_kind == Op::Select)
  {
    // assuming the array itself doesn't need to be casted
    // only the index
    // we have no support for or issue with that
    return make_term(
        Op::Select,
        terms[0],
        cast_term(terms[1], terms[0]->get_sort()->get_indexsort()));
  }
  // case 8 -- special case for ARRAY store
  else if (op_kind == Op::Store)
  {
    // assuming the array itself doesn't need to be casted
    // only the index
    // we have no support for or issue with that
    Sort arrsort = terms[0]->get_sort();
    return make_term(Op::Store,
                     terms[0],
                     cast_term(terms[1], arrsort->get_indexsort()),
                     cast_term(terms[2], arrsort->get_elemsort()));
  }
  // case 9 -- special case for FUNCTION
  else if (op_kind == Op::Apply)
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
    return make_term(Op::Apply, casted_children);
  }
  // case 10 -- a quantifier, whose body is a bit-vector of width one in a
  // solver that aliases the two
  else if (op_kind == Op::Forall || op_kind == Op::Exists)
  {
    TermVec casted_children(terms.begin(), terms.end() - 1);
    casted_children.push_back(
        cast_term(terms.back(), make_sort(SortKind::BOOL)));
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

}  // namespace smt
