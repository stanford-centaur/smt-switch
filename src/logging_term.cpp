/*!
 * \file logging_term.cpp
 * \brief Class that wraps another Term object and maintains the expected Op and
 *        children (for solvers that rewrite terms on the fly)
 * \author Makai Mann
 * \date 2020
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/logging_term.h"

#include <cstddef>
#include <cstdint>
#include <memory>
#include <utility>
#include <vector>

#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"
#include "smt-switch/utils.h"

namespace smt {

/* LoggingTerm */

LoggingTerm::LoggingTerm(Term t, Sort s, Op o, TermVec c, std::size_t id)
    : wrapped_term(std::move(t)),
      sort(std::move(s)),
      op(o),
      children(c.empty() ? nullptr
                         : std::make_shared<const TermVec>(std::move(c))),
      id_(id)
{
}

LoggingTerm::LoggingTerm(
    Term t, Sort s, Op o, TermVec c, std::string r, bool symbol, std::size_t id)
    : wrapped_term(std::move(t)),
      sort(std::move(s)),
      op(o),
      children(c.empty() ? nullptr
                         : std::make_shared<const TermVec>(std::move(c))),
      repr(std::move(r)),
      is_sym(symbol),
      is_par(!symbol),
      id_(id)
{
}

LoggingTerm::LoggingTerm(Term t, Sort s, std::string r, std::size_t id)
    : wrapped_term(std::move(t)),
      sort(std::move(s)),
      repr(std::move(r)),
      id_(id)
{
}

// implemented

std::size_t LoggingTerm::get_id() const { return id_; }

bool LoggingTerm::compare(const Term & t) const
{
  // This methods compares two LoggingTerms
  // it is a particularly tricky implementation compared to the
  // compare method in other implementations of AbsTerm
  // If the underlying terms are different, then this will return false
  // However, even if the underlying terms are the same, this might
  // still need to return false. It needs to check that the sort,
  // operator and children are the same to keep the contract that
  // the logging term hides sort aliasing and term rewriting
  // Furthermore, we want to avoid recursively calling compare
  // on the whole term DAG because the children are also LoggingTerms
  // which rely on this method for equality
  // Because we perform hash-consing, we can only compare the pointer values
  // to compare children. See the use of .get() on the children below.
  // However, we do not just compare the pointer value of this term with
  // the pointer value of the argument t.
  // This is because we actually need to use this compare method for equality
  // when looking up this term in the hash table to perform hash-consing.
  // which is done when constructing the term. At this point, it still has
  // a different pointer value.
  // Thus, we cannot count on the pointers of this term and the argument t
  // to be equal. Instead we want to check that they represent the same term.
  // which is true if the underlying terms are the same, and they both have
  // the same Op, Sort, and children.

  if (!t)
  {
    // not equivalent to null term
    return false;
  }

  std::shared_ptr<LoggingTerm> lt = std::dynamic_pointer_cast<LoggingTerm>(t);
  if (!lt)
  {
    return false;
  }

  // compare wrapped term and the LoggingSort
  // this handles values (e.g. null operators and no children)
  // and because of the sort comparison also handles sort aliasing
  // of the wrapped solver
  if (wrapped_term != lt->wrapped_term || sort != lt->sort)
  {
    return false;
  }

  // compare op
  if (op != lt->op)
  {
    return false;
  }

  // finally need to make sure all children match
  // this is the most expensive check, so we do it last
  if (!children || !lt->children)
  {
    return !children && !lt->children;
  }
  if (children->size() != lt->children->size())
  {
    return false;
  }
  else
  {
    for (std::size_t i = 0; i < children->size(); i++)
    {
      // because of hash-consing, we can compare the pointers
      // otherwise would recursively call compare on the LoggingTerm children
      // Note: calling get() instead of comparing the Term shared_ptrs directly
      // because operator== is overloaded for Terms such that it uses the
      // compare method of the underlying object (i.e. it would be a recursive
      // call to compare)
      if ((*children)[i].get() != (*lt->children)[i].get())
      {
        return false;
      }
    }
  }
  return true;
}

Op LoggingTerm::get_op() const { return op; }

Sort LoggingTerm::get_sort() const { return sort; }

std::string LoggingTerm::to_string() const
{
  if (!repr.empty())
  {
    return repr;
  }

  // rely on underlying term for values
  // this is because values are often produced by the underlying solver
  // e.g. from get_value
  // so we couldn't assign a string at the smt-switch level
  if (op.is_null() && is_value())
  {
    return wrapped_term->print_value_as(sort->get_sort_kind());
  }
  else if (op.is_null())
  {
    // A leaf the backend made that is not a value, such as some get_value
    // results, which only the backend can print
    return wrapped_term->to_string();
  }
  else
  {
    repr = smtlib_application(op, children ? *children : TermVec());
    return repr;
  }
}

std::wstring LoggingTerm::getStringValue() const
{
  return wrapped_term->getStringValue();
}

bool LoggingTerm::is_symbol() const
{
  // functions, parameters, and symbolic constants are all symbols
  return is_sym || is_par;
}

bool LoggingTerm::is_param() const { return op.is_null() && is_par; }

bool LoggingTerm::is_symbolic_const() const
{
  return is_sym && sort->get_sort_kind() != FUNCTION;
}

std::size_t LoggingTerm::get_num_children() const
{
  return children ? children->size() : 0;
}

Term LoggingTerm::get_child(std::size_t i) const { return (*children)[i]; }

// dispatched to underlying term

std::size_t LoggingTerm::hash() const { return wrapped_term->hash(); }

// check if op is null because a non-value
// may have been simplified to a value by the underlying solver
bool LoggingTerm::is_value() const
{
  if (op.prim_op == Apply_Constructor)
  {
    // The first child is the constructor itself.
    for (std::size_t i = 1; i < children->size(); ++i)
    {
      if (!(*children)[i]->is_value())
      {
        return false;
      }
    }
    return true;
  }
  if (op.prim_op == Store)
  {
    // SMT-LIB's ArraysEx makes a store of a value into an array value a value
    for (const Term & c : *children)
    {
      if (!c->is_value())
      {
        return false;
      }
    }
    return true;
  }
  return op.is_null() && wrapped_term->is_value();
}

std::string LoggingTerm::get_constructor_name() const
{
  SortKind sk = sort->get_sort_kind();
  if (sk != CONSTRUCTOR && sk != TESTER)
  {
    throw IncorrectUsageException(
        "Only a constructor or a tester has a constructor name");
  }
  return wrapped_term->get_constructor_name();
}

std::string LoggingTerm::get_param_name() const
{
  if (!is_param())
  {
    throw IncorrectUsageException("Only a param has a param name");
  }
  return wrapped_term->get_param_name();
}

std::string LoggingTerm::get_selector_name() const
{
  if (sort->get_sort_kind() != SELECTOR)
  {
    throw IncorrectUsageException("Only a selector has a selector name");
  }
  return wrapped_term->get_selector_name();
}

std::string LoggingTerm::get_symbol_name() const
{
  if (!is_sym)
  {
    throw IncorrectUsageException(
        "Only a symbol that is not a param has a symbol name");
  }
  return wrapped_term->get_symbol_name();
}

std::uint64_t LoggingTerm::to_int() const { return wrapped_term->to_int(); }

std::int64_t LoggingTerm::to_signed_int() const
{
  return wrapped_term->to_signed_int();
}

bool LoggingTerm::to_bool() const
{
  // the logged sort tells Booleans from 1-bit bit-vectors where the
  // underlying solver aliases them
  if (get_sort()->get_sort_kind() != BOOL)
  {
    throw IncorrectUsageException("Can't convert " + to_string()
                                  + " to a Boolean: it is not a Boolean value");
  }
  return wrapped_term->to_bool();
}

std::string LoggingTerm::print_value_as(SortKind sk) const
{
  return wrapped_term->print_value_as(sk);
}

}  // namespace smt
