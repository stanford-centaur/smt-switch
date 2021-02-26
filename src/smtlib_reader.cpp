#include "smtlib_reader.h"

#include "assert.h"
#include "smtlibparser.h"
#include "smtlibparser_maps.h"

using namespace std;

namespace smt {

// TODO remove this if never used
Command str_to_command(std::string cmd)
{
  if (cmd == "set-logic")
  {
    return SETLOGIC;
  }
  else if (cmd == "set-option")
  {
    return SETOPT;
  }
  else if (cmd == "declare-const")
  {
    return DECLARECONST;
  }
  else if (cmd == "define-fun")
  {
    return DEFINEFUN;
  }
  else if (cmd == "assert")
  {
    return ASSERT;
  }
  else if (cmd == "check-sat")
  {
    return CHECKSAT;
  }
  else if (cmd == "check-sat-assuming")
  {
    return CHECKSATASSUMING;
  }
  else if (cmd == "push")
  {
    return PUSH;
  }
  else if (cmd == "pop")
  {
    return POP;
  }
  else
  {
    throw SmtException("SmtLibReader Unknown smt-lib command: " + cmd);
  }
}

SmtLibReader::SmtLibReader(smt::SmtSolver & solver)
    : solver_(solver),
      current_command_(Command::NONE),
      def_arg_prefix_("__defvar_")
{
  // dedicated true/false symbols
  // done this way because true/false can be used in other places
  // for example, when setting options
  symbols_["true"] = solver_->make_term(true);
  symbols_["false"] = solver_->make_term(false);
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

void SmtLibReader::set_command(Command cmd)
{
  if (current_command_ == DEFINEFUN)
  {
    // clear the current argument mapping
    tmp_arg_mapping_.clear();
    sort_tmp_arg_mapping_.clear();
  }
  current_command_ = cmd;
}

Term SmtLibReader::lookup_symbol(const string & sym)
{
  Term symbol_term;
  assert(!symbol_term);
  auto it = symbols_.find(sym);
  if (it != symbols_.end())
  {
    symbol_term = it->second;
    assert(symbol_term);
  }
  return symbol_term;
}

Term SmtLibReader::lookup_arg(const string & name)
{
  assert(current_command_ == DEFINEFUN);
  auto it = tmp_arg_mapping_.find(name);
  if (it != tmp_arg_mapping_.end())
  {
    return it->second;
  }
  return lookup_symbol(name);
}

void SmtLibReader::new_symbol(const std::string & name, const smt::Sort & sort)
{
  Term fresh_symbol = solver_->make_symbol(name, sort);
  symbols_[name] = fresh_symbol;
}

PrimOp SmtLibReader::lookup_primop(const std::string & str)
{
  return str2primop.at(str);
}

void SmtLibReader::define_fun(const string & name,
                              const Term & def,
                              const TermVec & args)
{
  defs_[name] = def;
  def_args_[name] = args;
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
  assert(current_command_ == DEFINEFUN);
  // find the right id for this argument
  // can't associate with same variable as another argument for this define-fun
  size_t id = 0;
  auto it = sort_tmp_arg_mapping_.find(sort);
  if (it != sort_tmp_arg_mapping_.end())
  {
    id = it->second.size();
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

  tmp_arg_mapping_[name] = tmpvar;
  sort_tmp_arg_mapping_[sort][name] = tmpvar;
  return tmpvar;
}

}  // namespace smt
