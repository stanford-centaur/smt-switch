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

// maps logic string to vector of theories included in the logic
const unordered_map<string, vector<string>> logic_theory_map(
    { { "A", { "A" } },
      { "AX", { "A" } },
      { "BV", { "BV" } },
      { "DT", { "DT" } },
      { "IDL", { "IA" } },
      { "LIA", { "IA" } },
      { "LIRA", { "IA", "RA", "IRA" } },
      { "LRA", { "RA" } },
      { "NIA", { "IA" } },
      { "NIRA", { "IA", "RA", "IRA" } },
      { "NRA", { "RA" } },
      { "RDL", { "RA" } },
      { "UF", { "UF" } } });

// maps logic string to vector of associated SortKinds for that logic
const unordered_map<string, vector<SortKind>> logic_sortkind_map(
    { { "A", { ARRAY } },
      { "AX", { ARRAY } },
      { "BV", { BV } },
      { "DT", {} },
      { "IDL", { INT } },
      { "LIA", { INT } },
      { "LIRA", { INT, REAL } },
      { "LRA", { REAL } },
      { "NIA", { INT } },
      { "NIRA", { INT, REAL } },
      { "NRA", { REAL } },
      { "RDL", { REAL } },
      { "UF", { FUNCTION } } });

SmtLibReader::SmtLibReader(smt::SmtSolver & solver, bool strict)
    : solver_(solver),
      strict_(strict),
      logic_("UNSET"),
      allow_ufs_(false),
      def_arg_prefix_("__defvar_"),
      // logic always includes core theory
      primops_(strict_theory2opmap.at("Core")),
      // always have sort Bool available
      sortkinds_({ { "Bool", BOOL } })
{
  // dedicated true/false symbols
  // done this way because true/false can be used in other places
  // for example, when setting options
  assert(!global_symbols_.current_scope());
}

int SmtLibReader::parse(const std::string & f)
{
  file = f;
  location_.initialize(&file);
  scan_begin();
  int res;
  try
  {
    smtlib::parser parse(*this);
    // commented from calc++ example
    // parse.set_debug_level (trace_parsing);
    res = parse();
  }
  catch (const SmtException & e)
  {
    // need to end scan even if threw an exception
    scan_end();
    throw e;
  }
  scan_end();
  return res;
}

void SmtLibReader::set_logic(const string & logic)
{
  if (logic == "ALL")
  {
    set_logic_all();
    return;
  }

  solver_->set_logic(logic);
  logic_ = logic;

  // process logic to get available operator symbols
  string processed_logic = logic;
  if (processed_logic.substr(0, 3) == "QF_")
  {
    // parser doesn't distinguish -- let solver complain
    // if using quantifiers in quantifier-free logic
    processed_logic = processed_logic.substr(3, processed_logic.length() - 3);
  }

  unordered_set<string> theories;
  size_t logic_size;
  while (logic_size = processed_logic.size())
  {
    // all existing theories have abbreviations of length 4 or shorter
    for (size_t len = 1; len <= 4; len++)
    {
      string sub = processed_logic.substr(0, len);
      if (logic_theory_map.find(sub) != logic_theory_map.end())
      {
        // add operators for this theory
        for (const auto & theory : logic_theory_map.at(sub))
        {
          theories.insert(theory);
          for (const auto & elem : strict_theory2opmap.at(theory))
          {
            primops_.insert(elem);
          }
        }

        processed_logic =
            processed_logic.substr(len, processed_logic.length() - len);

        // should also be in logic_sortkind_map
        assert(logic_sortkind_map.find(sub) != logic_sortkind_map.end());

        if (sub == "UF")
        {
          // special-case for UF, still want to allow sorts
          // named FUNCTION, so don't add to sortkinds_
          // instead, just set the allow_ufs_ flag
          allow_ufs_ = true;
        }
        else
        {
          for (const SortKind sk : logic_sortkind_map.at(sub))
          {
            sortkinds_[smt::to_string(sk)] = sk;
          }
        }
        break;
      }
    }

    if (processed_logic.size() == logic_size)
    {
      throw SmtException("Failed to interpret logic: " + logic);
    }
  }

  if (!strict_)
  {
    // add non-strict operators
    bool bv_theory = theories.find("BV") != theories.end();
    bool int_theory = theories.find("IA") != theories.end();
    vector<string> theory_combs;

    if (int_theory)
    {
      theory_combs.push_back("IA");
    }
    if (int_theory && bv_theory)
    {
      theory_combs.push_back("BVIA");
    }

    for (const auto & comb : theory_combs)
    {
      for (const auto & elem : nonstrict_theory2opmap.at(comb))
      {
        primops_.insert(elem);
      }
    }
  }
}

void SmtLibReader::set_logic_all()
{
  try
  {
    solver_->set_logic("ALL");
  }
  catch (SmtException & e)
  {
    ;
  }

  logic_ = "ALL";

  // enable UFs manually
  allow_ufs_ = true;

  // add all strict operators
  for (const auto & tmap : strict_theory2opmap)
  {
    for (const auto & elem : tmap.second)
    {
      primops_.insert(elem);
    }
  }

  // add sorts
  for (const auto & elem : logic_sortkind_map)
  {
    for (const SortKind & sk : elem.second)
    {
      sortkinds_[smt::to_string(sk)] = sk;
    }
  }

  if (!strict_)
  {
    // add non-strict operators
    for (const auto & tmap : nonstrict_theory2opmap)
    {
      for (const auto & elem : tmap.second)
      {
        primops_.insert(elem);
      }
    }
  }
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

void SmtLibReader::push(uint64_t num)
{
  for (size_t i = 0; i < num; ++i)
  {
    global_symbols_.push_scope();
  }
  solver_->push(num);
}

void SmtLibReader::pop(uint64_t num)
{
  for (size_t i = 0; i < num; ++i)
  {
    global_symbols_.pop_scope();
  }
  solver_->pop(num);
}

void SmtLibReader::term_attribute(const Term & term,
                                  const string & keyword,
                                  const string & value)
{
  cerr << "Warning: ignoring attribute :" << keyword << " " << value << endl;
}

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

  if (sym == "true")
  {
    return solver_->make_term(true);
  }
  else if (sym == "false")
  {
    return solver_->make_term(false);
  }

  if (current_scope())
  {
    // check scoped variables before global symbols
    // shadowing semantics
    symbol_term = arg_param_map_.get_symbol(sym);
    if (symbol_term)
    {
      return symbol_term;
    }
  }

  assert(!symbol_term);
  symbol_term = global_symbols_.get_symbol(sym);
  return symbol_term;
}

void SmtLibReader::new_symbol(const std::string & name, const smt::Sort & sort)
{
  if (global_symbols_.get_symbol(name))
  {
    throw SmtException("Re-declaring symbol: " + name);
  }

  auto it = all_symbols_.find(name);
  if (it != all_symbols_.end())
  {
    if (it->second->get_sort() != sort)
    {
      throw SmtException("Current Limitation: cannot re-declare symbol " + name
                         + " with a different sort");
    }
    global_symbols_.add_mapping(name, it->second);
    return;
  }

  if (strict_ && !allow_ufs_ && sort->get_sort_kind() == FUNCTION)
  {
    throw IncorrectUsageException("Tried to declare UF, but current logic "
                                  + logic_ + " does not support UFs");
  }

  Term fresh_symbol = solver_->make_symbol(name, sort);
  global_symbols_.add_mapping(name, fresh_symbol);
  all_symbols_[name] = fresh_symbol;
}

PrimOp SmtLibReader::lookup_primop(const std::string & str)
{
  auto it = primops_.find(str);
  if (it != primops_.end())
  {
    return it->second;
  }
  else
  {
    // returning null because not in set of operators
    // (at least for the logic that was set)
    return NUM_OPS_AND_NULL;
  }
}

pair<PrimOp, Term> SmtLibReader::lookup_apply_op_term(const string & s0,
                                                      const string & s1)
{
  if (s0 != "is")
  {
    throw SmtException("Unsupported indexed operator starting with " + s0);
  }
  else if (strict_ && primops_.find("DT") == primops_.end())
  {
    throw SmtException("Datatypes not enabled but got tester for " + s1);
  }

  PrimOp po = Apply_Tester;
  // there should be an affiliated constructor
  Term constructor = lookup_constructor(s1);
  assert(constructor);
  // get datatype sort from the constructor
  Sort dtsort = constructor->get_sort()->get_codomain_sort();
  Term tester = solver_->get_tester(dtsort, s1);

  assert(tester);
  return { po, tester };
}

SortKind SmtLibReader::lookup_sortkind(const std::string & str)
{
  SortKind sk = NUM_SORT_KINDS;
  auto it = sortkinds_.find(str);
  if (it != sortkinds_.end())
  {
    sk = it->second;
  }
  return sk;
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
    global_symbols_.add_mapping(name, def);
  }
}

Term SmtLibReader::apply_define_fun(const string & defname,
                                    const TermVec & args)
{
  UnorderedTermMap subs_map;
  size_t num_args = args.size();
  assert(num_args); // apply_define_fun only for defines which take arguments

  auto it = defs_.find(defname);

  if (it == defs_.end())
  {
    throw SmtException("Unknown function: " + defname);
  }

  Term def = it->second;

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
  unordered_map<Sort, size_t> & current_scope_sort_ids = sort_arg_ids_.back();
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
    tmpvar = solver_->make_symbol(def_arg_prefix_ + sort->to_string() +
                                  std::to_string(id), sort);
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

void SmtLibReader::define_sort(const string & name,
                               const Sort & sort,
                               bool redefine)
{
  if (sortkinds_.find(name) != sortkinds_.end())
  {
    throw IncorrectUsageException("Cannot define sort " + name + " in logic "
                                  + logic_);
  }
  else if (!redefine && defined_sorts_.find(name) != defined_sorts_.end())
  {
    throw SmtException("Cannot re-define sort with name " + name);
  }
  defined_sorts_[name] = sort;
}

Sort SmtLibReader::lookup_sort(const string & name)
{
  auto it = defined_sorts_.find(name);
  if (it == defined_sorts_.end())
  {
    throw SmtException("Unknown defined sort symbol " + name);
  }
  return it->second;
}

Term SmtLibReader::create_param(const string & name, const Sort & sort)
{
  assert(current_scope());
  Term param;
  // some solvers don't allow re-using parameter names
  // need to find a fresh one
  size_t id = 0;
  while (!param)
  {
    try
    {
      param = solver_->make_param(name + "__param_" + std::to_string(id), sort);
    }
    catch (SmtException & e)
    {
      id++;
      if (id > 100000)
      {
        throw SmtException(
            "Could not find a fresh parameter after 100,000 tries");
      }
    }
  }
  assert(param);
  arg_param_map_.add_mapping(name, param);
  return param;
}

void SmtLibReader::let_binding(const string & sym, const Term & term)
{
  assert(current_scope());
  arg_param_map_.add_mapping(sym, term);
}

void SmtLibReader::declare_datatypes(
    vector<DatatypeDecl> & dtspecs,
    const vector<Sort> & fwdrefs,
    const vector<ConstructorDecVec> & cons_list)
{
  assert(dtspecs.size() == fwdrefs.size());
  assert(fwdrefs.size() == cons_list.size());

  size_t num_dt = dtspecs.size();
  for (size_t i = 0; i < num_dt; ++i)
  {
    DatatypeDecl & dtspec = dtspecs[i];
    const Sort & fwdref = fwdrefs[i];
    const ConstructorDecVec & cons = cons_list[i];
    string sortname = fwdref->get_uninterpreted_name();
    for (const auto & c : cons)
    {
      DatatypeConstructorDecl condecl =
          solver_->make_datatype_constructor_decl(c.first);
      solver_->add_constructor(dtspec, condecl);
      for (const auto & sel : c.second)
      {
        solver_->add_selector(condecl, sel.first, sel.second);
      }
    }
  }

  // resolve the finished datatype sort and record the mapping
  UnorderedSortSet uninterp_sorts;
  uninterp_sorts.insert(fwdrefs.begin(), fwdrefs.end());
  SortVec dtsorts = solver_->make_datatype_sorts(dtspecs, uninterp_sorts);
  for (const auto & dtsort : dtsorts)
  {
    define_sort(
        dtsort->to_string(), dtsort, true);  // boolean flag allows redefining
  }

  for (size_t i = 0; i < num_dt; ++i)
  {
    Sort dtsort = dtsorts[i];
    // using define-fun to record names of constructor
    // used later to get term back
    // Note: even though we have get_constructor,
    // it needs to know which sort the constructor is affiliated with
    // plus this fits into parser infrastructure better
    for (const auto & c : cons_list[i])
    {
      define_constructor(c.first, solver_->get_constructor(dtsort, c.first));
      for (const auto & sel : c.second)
      {
        define_selector(sel.first,
                        solver_->get_selector(dtsort, c.first, sel.first));
      }
    }
  }
}

Term SmtLibReader::lookup_constructor(const string & sym) const
{
  Term res;
  auto it = constructors_.find(sym);
  if (it != constructors_.end())
  {
    res = it->second;
  }
  return res;
}

Term SmtLibReader::lookup_selector(const string & sym) const
{
  Term res;
  auto it = selectors_.find(sym);
  if (it != selectors_.end())
  {
    res = it->second;
  }
  return res;
}

// protected methods

void SmtLibReader::define_constructor(const string & sym, const Term & cons)
{
  if (constructors_.find(sym) != constructors_.end())
  {
    throw SmtException("Constructor named " + sym + " already defined");
  }
  constructors_[sym] = cons;
}

void SmtLibReader::define_selector(const string & sym, const Term & sel)
{
  if (selectors_.find(sym) != selectors_.end())
  {
    throw SmtException("Selector named " + sym + " already defined");
  }
  selectors_[sym] = sel;
}

}  // namespace smt
