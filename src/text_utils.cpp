/*!
 * \file text_utils.cpp
 * \brief Helpers for writing and reading SMT-LIB text
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include "smt-switch/text_utils.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <locale>
#include <map>
#include <memory>
#include <sstream>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "smt-switch/datatype.h"
#include "smt-switch/exceptions.h"
#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"
#include "smt-switch/term_visitor.h"
#include "smt-switch/visit_result.h"

namespace smt {

namespace {

// SMT-LIB 2.6 reserves these words (Section 3.1) and every command name
// (Figure 3.6), so none of them is a simple symbol.
constexpr std::string_view smtlib_reserved_words[] = {
  "!",
  "_",
  "BINARY",
  "DECIMAL",
  "HEXADECIMAL",
  "NUMERAL",
  "STRING",
  "as",
  "assert",
  "check-sat",
  "check-sat-assuming",
  "declare-const",
  "declare-datatype",
  "declare-datatypes",
  "declare-fun",
  "declare-sort",
  "define-fun",
  "define-fun-rec",
  "define-funs-rec",
  "define-sort",
  "echo",
  "exists",
  "exit",
  "forall",
  "get-assertions",
  "get-assignment",
  "get-info",
  "get-model",
  "get-option",
  "get-proof",
  "get-unsat-assumptions",
  "get-unsat-core",
  "get-value",
  "let",
  "match",
  "par",
  "pop",
  "push",
  "reset",
  "reset-assertions",
  "set-info",
  "set-logic",
  "set-option",
};

template <class T>
std::string get_text(const T & x,
                     const std::function<std::string(const T &)> & text)
{
  return text ? text(x) : x->to_string();
}

// Adds the uninterpreted sorts, sort constructors and datatypes that
// declaring a term of sort s needs, keyed by name, to those found so far.
// Distinct ones with the same name are all kept; an applied sort adds its
// constructor, once whatever it is applied to.
void collect_declared_sorts(const Sort & s,
                            std::map<std::string, SortVec> & sorts,
                            std::map<std::string, Sort> & datatypes)
{
  // no default, so that -Wswitch reports an enumerator without a case
  switch (s->get_sort_kind())
  {
    case ARRAY:
      collect_declared_sorts(s->get_indexsort(), sorts, datatypes);
      collect_declared_sorts(s->get_elemsort(), sorts, datatypes);
      break;
    case FUNCTION:
      for (const Sort & d : s->get_domain_sorts())
      {
        collect_declared_sorts(d, sorts, datatypes);
      }
      collect_declared_sorts(s->get_codomain_sort(), sorts, datatypes);
      break;
    case UNINTERPRETED: {
      SortVec params = s->get_uninterpreted_param_sorts();
      Sort declared = params.empty() ? s : s->get_uninterpreted_constructor();
      SortVec & named = sorts[declared->get_uninterpreted_name()];
      if (std::find(named.begin(), named.end(), declared) == named.end())
      {
        named.push_back(declared);
      }
      for (const Sort & p : params)
      {
        collect_declared_sorts(p, sorts, datatypes);
      }
      break;
    }
    case DATATYPE: {
      auto [found, added] = datatypes.emplace(s->get_datatype()->get_name(), s);
      // a datatype found before may be the sort of its own selectors
      if (!added)
      {
        if (found->second != s)
        {
          throw NotImplementedException(
              "smtlib::benchmark cannot declare two datatypes named "
              + found->first);
        }
        break;
      }
      Datatype dt = s->get_datatype();
      for (const std::string & cons : dt->get_constructor_names())
      {
        for (const std::string & sel : dt->get_selector_names(cons))
        {
          collect_declared_sorts(
              dt->get_selector_sort(cons, sel), sorts, datatypes);
        }
      }
      break;
    }
    // nothing to declare, and the datatypes of constructors, selectors
    // and testers are met through their arguments and results
    case BOOL:
    case BV:
    case INT:
    case REAL:
    case STRING:
    case UNINTERPRETED_CONS:
    case CONSTRUCTOR:
    case SELECTOR:
    case TESTER:
    case NUM_SORT_KINDS: break;
  }
}

// Writes sorts and terms as SMT-LIB, each renamed sort by its new name.
struct SortRenamer
{
  const std::unordered_map<Sort, std::string> & renamed;

  std::string operator()(const Sort & s) const
  {
    auto it = renamed.find(s);
    if (it != renamed.end())
    {
      return smtlib::quote_symbol(it->second);
    }
    SortKind sk = s->get_sort_kind();
    if (sk == ARRAY)
    {
      return "(Array " + (*this)(s->get_indexsort()) + " "
             + (*this)(s->get_elemsort()) + ")";
    }
    if (sk == UNINTERPRETED && !s->get_uninterpreted_param_sorts().empty())
    {
      // an applied sort is written with its constructor's name
      auto con = renamed.find(s->get_uninterpreted_constructor());
      std::string res =
          "("
          + smtlib::quote_symbol(
              con != renamed.end() ? con->second : s->get_uninterpreted_name());
      for (const Sort & p : s->get_uninterpreted_param_sorts())
      {
        res += " " + (*this)(p);
      }
      return res + ")";
    }
    return s->to_string();
  }

  std::string operator()(const Term & t) const
  {
    Op op = t->get_op();
    if (!op.is_null())
    {
      return smtlib::application(
          op, TermVec(t->begin(), t->end()), *this, *this);
    }
    // a constant array is the one leaf with a child, its value
    if (t->get_sort()->get_sort_kind() == ARRAY && t->begin() != t->end())
    {
      return smtlib::const_array((*this)(t->get_sort()), (*this)(*t->begin()));
    }
    return t->to_string();
  }
};

// Collects what terms need declared, each kind by name
class DeclarationsVisitor : public TermVisitor
{
 public:
  DeclarationsVisitor(std::map<std::string, Term> & symbols,
                      std::map<std::string, SortVec> & sorts,
                      std::map<std::string, Sort> & datatypes)
      : symbols_(symbols), sorts_(sorts), datatypes_(datatypes)
  {
  }

 protected:
  VisitResult visit_term(const Term & term) override
  {
    // a param is a symbol too, but its quantifier binds it
    if (term->is_symbol() && !term->is_param())
    {
      symbols_.emplace(term->to_string(), term);
    }
    collect_declared_sorts(term->get_sort(), sorts_, datatypes_);
    return VisitResult::Continue;
  }

 private:
  std::map<std::string, Term> & symbols_;
  std::map<std::string, SortVec> & sorts_;
  std::map<std::string, Sort> & datatypes_;
};

}  // namespace

namespace smtlib {

std::string quote_symbol(const std::string & s)
{
  if (s.empty())
  {
    return "||";
  }
  for (std::string_view reserved : smtlib_reserved_words)
  {
    if (s == reserved)
    {
      return "|" + s + "|";
    }
  }
  const std::locale & ascii = std::locale::classic();
  if (std::isdigit(s[0], ascii))
  {
    return "|" + s + "|";
  }
  const std::string punctuation = "~!@$%^&*_-+=<>.?/";
  for (char c : s)
  {
    if (!std::isalnum(c, ascii) && punctuation.find(c) == std::string::npos)
    {
      return "|" + s + "|";
    }
  }
  return s;
}

std::string unquote_symbol(const std::string & s)
{
  if (s.size() >= 2 && s.front() == '|' && s.back() == '|')
  {
    return s.substr(1, s.size() - 2);
  }
  return s;
}

std::string application(
    const Op & op,
    const TermVec & children,
    const std::function<std::string(const Term &)> & term_text,
    const std::function<std::string(const Sort &)> & sort_text)
{
  if (op.prim_op == Apply_Constructor && children.size() == 1)
  {
    return get_text(children[0], term_text);
  }
  if (op.prim_op == Forall || op.prim_op == Exists)
  {
    const Term & var = children[0];
    return "(" + op.to_string() + " ((" + get_text(var, term_text) + " "
           + get_text(var->get_sort(), sort_text) + ")) "
           + get_text(children[1], term_text) + ")";
  }
  const bool bv_power =
      op.prim_op == Pow && children[0]->get_sort()->get_sort_kind() == BV;
  if (op.prim_op == Pow && children[1]->is_value()
      && (bv_power || children[1]->to_signed_int() >= 2))
  {
    std::string res = bv_power ? "(bvmul" : "(*";
    for (std::uint64_t i = children[1]->to_int(); i > 0; --i)
    {
      res += " " + get_text(children[0], term_text);
    }
    return res + ")";
  }
  std::string res = "(";
  if (!is_apply(op.prim_op))
  {
    res += op.to_string() + " ";
  }
  for (std::size_t i = 0; i < children.size(); ++i)
  {
    if (i > 0)
    {
      res += " ";
    }
    res += get_text(children[i], term_text);
  }
  return res + ")";
}

std::string const_array(const std::string & sort, const std::string & value)
{
  return "((as const " + sort + ") " + value + ")";
}

std::string arith_value(SortKind sk, const std::string & value)
{
  bool negative = value.find('-') == 0;
  std::string magnitude =
      negative || value.find('+') == 0 ? value.substr(1) : value;
  // SMT-LIB numerals have no leading zeros, a decimal has digits on both
  // sides of its point, and a REAL value needs a decimal point for solvers
  // that do not convert an integer literal
  auto number_text = [sk](const std::string & number) {
    std::string::size_type point = number.find('.');
    std::string whole = number.substr(0, point);
    std::string::size_type first = whole.find_first_not_of('0');
    whole = first == std::string::npos ? "0" : whole.substr(first);
    if (point == std::string::npos)
    {
      return sk == REAL ? whole + ".0" : whole;
    }
    std::string fraction = number.substr(point + 1);
    return whole + "." + (fraction.empty() ? "0" : fraction);
  };
  // SMT-LIB numerals are never negative, and SMT-LIB has no fraction
  // literal, so a fraction is a division of two numbers
  std::string::size_type slash = magnitude.find('/');
  std::string repr = sk == REAL && slash != std::string::npos
                         ? "(/ " + number_text(magnitude.substr(0, slash)) + " "
                               + number_text(magnitude.substr(slash + 1)) + ")"
                         : number_text(magnitude);
  if (negative)
  {
    repr = "(- " + repr + ")";
  }
  return repr;
}

std::string declare_fun(
    const Term & symbol,
    const std::function<std::string(const Sort &)> & sort_text)
{
  Sort sort = symbol->get_sort();
  std::string domain;
  if (sort->get_sort_kind() == FUNCTION)
  {
    for (const Sort & d : sort->get_domain_sorts())
    {
      domain += (domain.empty() ? "" : " ") + get_text(d, sort_text);
    }
    sort = sort->get_codomain_sort();
  }
  std::string res = "(";
  res += DECLARE_FUN_STR;
  return res + " " + symbol->to_string() + " (" + domain + ") "
         + get_text(sort, sort_text) + ")";
}

std::string declare_datatypes(
    const SortVec & datatypes,
    const std::function<std::string(const Sort &)> & sort_text)
{
  if (datatypes.empty())
  {
    throw IncorrectUsageException(
        "SMT-LIB cannot declare an empty list of datatypes");
  }
  std::string names;
  std::string bodies;
  for (const Sort & s : datatypes)
  {
    Datatype dt = s->get_datatype();
    names += (names.empty() ? "(" : " (") + s->to_string() + " 0)";
    std::string constructors;
    for (const std::string & cons : dt->get_constructor_names())
    {
      constructors += (constructors.empty() ? "(" : " (") + quote_symbol(cons);
      for (const std::string & sel : dt->get_selector_names(cons))
      {
        constructors += " (" + quote_symbol(sel) + " "
                        + get_text(dt->get_selector_sort(cons, sel), sort_text)
                        + ")";
      }
      constructors += ")";
    }
    bodies += (bodies.empty() ? "(" : " (") + constructors + ")";
  }
  std::string res = "(";
  res += DECLARE_DATATYPE_STR;
  return res + " (" + names + ") (" + bodies + "))";
}

void benchmark(std::ostream & out,
               const std::string & logic,
               const TermVec & assertions)
{
  // what the assertions need declared, each kind by name, so that the same
  // assertions always dump alike
  std::map<std::string, Term> symbols;
  std::map<std::string, SortVec> sorts;
  std::map<std::string, Sort> datatypes;
  DeclarationsVisitor declarations(symbols, sorts, datatypes);
  // the last assertion first, which decides which of two sorts of the same
  // name keeps it
  for (auto it = assertions.rbegin(); it != assertions.rend(); ++it)
  {
    declarations.visit(*it);
  }

  // SMT-LIB cannot declare two sorts with the same name, but a sort's name
  // carries no semantic meaning on its own, so duplicates are renamed.
  std::unordered_map<Sort, std::string> renamed;
  std::map<std::string, Sort> declared;
  for (const auto & [name, named] : sorts)
  {
    declared.emplace(name, named.front());
    for (std::size_t i = 1; i < named.size(); ++i)
    {
      std::uint64_t k = 0;
      std::string fresh;
      do
      {
        fresh = name + "_" + std::to_string(++k);
      } while (sorts.count(fresh) || datatypes.count(fresh)
               || declared.count(fresh));
      renamed.emplace(named[i], fresh);
      declared.emplace(fresh, named[i]);
    }
  }
  // without renamed sorts, everything is written by its to_string
  std::function<std::string(const Sort &)> sort_text;
  std::function<std::string(const Term &)> term_text;
  if (!renamed.empty())
  {
    sort_text = SortRenamer{ renamed };
    term_text = SortRenamer{ renamed };
  }

  out << "(" << SET_LOGIC_STR << " " << logic << ")\n";
  for (const auto & [name, s] : declared)
  {
    out << "(" << DECLARE_SORT_STR << " " << quote_symbol(name) << " "
        << s->get_arity() << ")\n";
  }
  if (!datatypes.empty())
  {
    SortVec dts;
    for (const auto & [name, s] : datatypes)
    {
      dts.push_back(s);
    }
    out << declare_datatypes(dts, sort_text) << "\n";
  }
  for (const auto & [name, symbol] : symbols)
  {
    out << declare_fun(symbol, sort_text) << "\n";
  }
  for (const Term & a : assertions)
  {
    out << "(" << ASSERT_STR << " " << get_text(a, term_text) << ")\n";
  }
  out << "(" << CHECK_SAT_STR << ")\n";
}

bool is_logic(const std::string & name)
{
  if (name == "ALL")
  {
    return true;
  }
  std::string_view rest = name;
  for (std::string_view prefix : { "QF_", "HO_" })
  {
    if (rest.substr(0, prefix.size()) == prefix)
    {
      rest.remove_prefix(prefix.size());
    }
  }
  if (rest.empty())
  {
    return false;
  }
  if (rest.substr(0, 2) == "AX")
  {
    rest.remove_prefix(2);
  }
  else if (rest.substr(0, 1) == "A")
  {
    rest.remove_prefix(1);
  }
  for (std::string_view theory : { "UF", "BV", "FP", "DT", "S" })
  {
    if (rest.substr(0, theory.size()) == theory)
    {
      rest.remove_prefix(theory.size());
    }
  }
  for (std::string_view arithmetic :
       { "IDL", "RDL", "LIA", "LRA", "LIRA", "NIA", "NRA", "NIRA", "EIA" })
  {
    if (rest == arithmetic)
    {
      return true;
    }
  }
  return rest.empty();
}

}  // namespace smtlib

}  // namespace smt
