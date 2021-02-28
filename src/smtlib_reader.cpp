/*********************                                                        */
/*! \file smtlib_reader.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Driver for reading SMT-LIB files. Depends on flex/bison
**
**
**/

#include "smtlib_reader.h"

#include "assert.h"
#include "smtlibparser.h"
#include "smtlibparser_maps.h"

using namespace std;

namespace smt {

SmtLibReader::SmtLibReader(smt::SmtSolver & solver)
    : solver_(solver),
      def_arg_prefix_("__defvar_")
{
  // dedicated true/false symbols
  // done this way because true/false can be used in other places
  // for example, when setting options
  global_symbols_["true"] = solver_->make_term(true);
  global_symbols_["false"] = solver_->make_term(false);
}

int SmtLibReader::parse(const std::string & f)
{
  file = f;
  location_.initialize(&file);
  scan_begin();
  yy::parser parse(*this);
  // commented from calc++ example
  // parse.set_debug_level (trace_parsing);
  int res = parse();
  scan_end();
  return res;
}

void SmtLibReader::set_logic(const string & logic)
{
  solver_->set_logic(logic);
}

void SmtLibReader::set_opt(const string & key, const string & val)
{
  solver_->set_opt(key, val);
}

void SmtLibReader::set_info(const string & key, const string & val)
{
  // No-Op for set-info by default
}

void SmtLibReader::assert_formula(const Term & assertion)
{
  solver_->assert_formula(assertion);
}

Result SmtLibReader::check_sat()
{
  Result r = solver_->check_sat();
  cout << r << endl;
  return r;
}

Result SmtLibReader::check_sat_assuming(const TermVec & assumptions)
{
  Result r = solver_->check_sat_assuming(assumptions);
  cout << r << endl;
  return r;
}

void SmtLibReader::push(uint64_t num) { solver_->push(num); }

void SmtLibReader::pop(uint64_t num) { solver_->pop(num); }

void SmtLibReader::push_scope()
{
  arg_param_map_.push_scope();
  sort_arg_ids_.push_back(std::unordered_map<smt::Sort, size_t>());
}

void SmtLibReader::pop_scope()
{
  arg_param_map_.pop_scope();
  sort_arg_ids_.pop_back();
}

Term SmtLibReader::lookup_symbol(const string & sym)
{
  Term symbol_term;
  assert(!symbol_term);

  if (current_scope())
  {
    // check scoped variables before global symbols
    // shadowing semantics
    try
    {
      return arg_param_map_.get_symbol(sym);
    }
    catch (std::out_of_range & e)
    {
      ;
    }
  }

  assert(!symbol_term);
  auto it = global_symbols_.find(sym);
  if (it != global_symbols_.end())
  {
    symbol_term = it->second;
    assert(symbol_term);
  }
  return symbol_term;
}

void SmtLibReader::new_symbol(const std::string & name, const smt::Sort & sort)
{
  Term fresh_symbol = solver_->make_symbol(name, sort);
  global_symbols_[name] = fresh_symbol;
}

PrimOp SmtLibReader::lookup_primop(const std::string & str)
{
  return str2primop.at(str);
}

void SmtLibReader::define_fun(const string & name,
                              const Term & def,
                              const TermVec & args)
{
  if (args.size())
  {
    // this is a function
    defs_[name] = def;
    def_args_[name] = args;
  }
  else
  {
    // this is just an alias for another term
    global_symbols_[name] = def;
  }
}

Term SmtLibReader::apply_define_fun(const string & defname,
                                    const TermVec & args)
{
  UnorderedTermMap subs_map;
  size_t num_args = args.size();

  auto it = defs_.find(defname);

  if (it == defs_.end())
  {
    throw SmtException("Unknown function: " + defname);
  }

  Term def = it->second;

  if (!num_args)
  {
    def;
  }

  if (num_args != def_args_.at(defname).size())
  {
    throw SmtException(defname
                       + " not applied to correct number of arguments.");
  }

  for (size_t i = 0; i < args.size(); ++i)
  {
    subs_map[def_args_.at(defname)[i]] = args[i];
  }

  return solver_->substitute(def, subs_map);
}

Term SmtLibReader::register_arg(const string & name, const Sort & sort)
{
  assert(current_scope());
  // find the right id for this argument
  // can't associate with same variable as another argument for this define-fun
  size_t id = 0;
  auto current_scope_sort_ids = sort_arg_ids_.back();
  auto it = current_scope_sort_ids.find(sort);
  if (it != current_scope_sort_ids.end())
  {
    id = it->second;
  }
  else
  {
    current_scope_sort_ids[sort] = 0;
  }

  Term tmpvar;
  if (id >= tmp_args_[sort].size())
  {
    tmpvar = solver_->make_symbol(def_arg_prefix_ + std::to_string(id), sort);
    tmp_args_[sort].push_back(tmpvar);
  }
  else
  {
    tmpvar = tmp_args_[sort].at(id);
  }
  assert(tmpvar);

  arg_param_map_.add_mapping(name, tmpvar);
  current_scope_sort_ids[sort]++;
  return tmpvar;
}

Term SmtLibReader::create_param(const string & name, const Sort & sort)
{
  assert(current_scope());
  Term param = solver_->make_param(name, sort);
  arg_param_map_.add_mapping(name, param);
  return param;
}

}  // namespace smt
