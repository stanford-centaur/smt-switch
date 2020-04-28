#include "api_trace_solver.h"

#include <fstream>

using namespace std;

const std::unordered_map<PrimOp, std::string> primop2apistr(
    { { And, "And" },
      { Or, "Or" },
      { Xor, "Xor" },
      { Not, "Not" },
      { Implies, "Implies" },
      { Iff, "Iff" },
      { Ite, "Ite" },
      { Equal, "Equal" },
      { Distinct, "Distinct" },
      { Apply, "Apply" },
      { Plus, "Plus" },
      { Minus, "Minus" },
      { Negate, "Negate" },
      { Mult, "Mult" },
      { Div, "Div" },
      { IntDiv, "IntDiv" },
      { Lt, "Lt" },
      { Le, "Le" },
      { Gt, "Gt" },
      { Ge, "Ge" },
      { Mod, "Mod" },
      { Abs, "Abs" },
      { Pow, "Pow" },
      { Concat, "Concat" },
      { Extract, "Extract" },
      { BVNot, "BVNot" },
      { BVNeg, "BVNeg" },
      { BVAnd, "BVAnd" },
      { BVOr, "BVOr" },
      { BVXor, "BVXor" },
      { BVNand, "BVNand" },
      { BVNor, "BVNor" },
      { BVXnor, "BVXnor" },
      { BVComp, "BVComp" },
      { BVAdd, "BVAdd" },
      { BVSub, "BVSub" },
      { BVMul, "BVMul" },
      { BVUdiv, "BVUdiv" },
      { BVSdiv, "BVSdiv" },
      { BVUrem, "BVUrem" },
      { BVSrem, "BVSrem" },
      { BVSmod, "BVSmod" },
      { BVShl, "BVShl" },
      { BVAshr, "BVAshr" },
      { BVLshr, "BVLshr" },
      { BVUlt, "BVUlt" },
      { BVUle, "BVUle" },
      { BVUgt, "BVUgt" },
      { BVUge, "BVUge" },
      { BVSlt, "BVSlt" },
      { BVSle, "BVSle" },
      { BVSgt, "BVSgt" },
      { BVSge, "BVSge" },
      { Zero_Extend, "Zero_Extend" },
      { Sign_Extend, "Sign_Extend" },
      { Repeat, "Repeat" },
      { Rotate_Left, "Rotate_Left" },
      { Rotate_Right, "Rotate_Right" },
      { Select, "Select" },
      { Store, "Store" } });

std::string op_to_api_str(Op op)
{
  std::string res = primop2apistr.at(op.prim_op);
  if (!op.num_idx)
  {
    return res;
  }
  else if (op.num_idx == 1)
  {
    res = "Op(" + res + ", " + std::to_string(op.idx0) + ")";
  }
  else if (op.num_idx == 2)
  {
    res = "Op(" + res + ", " + std::to_string(op.idx0) + ", "
          + std::to_string(op.idx1) + ")";
  }
  return res;
}

namespace smt {

void ApiTraceSolver::set_opt(const std::string option, const std::string value)
{
  trace_lines->push_back("s->set_opt(\"" + option + "\", \"" + value + "\");");
  sub_solver->set_opt(option, value);
}

void ApiTraceSolver::set_logic(const std::string logic)
{
  trace_lines->push_back("s->set_opt(\"" + logic + "\");");
  sub_solver->set_logic(logic);
}

void ApiTraceSolver::assert_formula(const Term & t)
{
  trace_lines->push_back("s->assert_formula("
                         + term2name->at((uintptr_t)t->get(0)) + ");");
  sub_solver->assert_formula(t);
}

Result ApiTraceSolver::check_sat()
{
  string result_name = "r" + std::to_string(*rid);
  (*rid)++;
  trace_lines->push_back("Result " + result_name + " = s->check_sat()");
  return sub_solver->check_sat();
}

Result ApiTraceSolver::check_sat_assuming(const TermVec & assumptions)
{
  string vec_input = "{";
  for (auto a : assumptions)
  {
    vec_input += term2name->at((uintptr_t)a->get()) + ",";
  }
  vec_input += "}";
  string result_name = "r" + std::to_string(*rid);
  (*rid)++;
  trace_lines->push_back("Result " + result_name + " = s->check_sat_assuming("
                         + vec_input + "});");
  return sub_solver->check_sat_assuming(assumptions);
}

void ApiTraceSolver::push(uint64_t num = 1)
{
  trace_lines->push_back("s->push(" + std::to_string(num) + ");");
  sub_solver->push(num);
}

void ApiTraceSolver::pop(uint64_t num = 1)
{
  trace_lines->push_back("s->pop(" + std::to_string(num) + ");");
  sub_solver->pop(num);
}

Term ApiTraceSolver::get_value(Term & t) const
{
  string node_name = "n" + std::to_string(*nid);
  (*nid)++;
  trace_lines->push_back("Term " + node_name + " = s->get_value("
                         + term2name->at((uintptr_t)t->get()) + ");");
  Term res = sub_solver->get_value(t);
  (*term2name)[(uintptr_t)res->get()] = node_name;
  return res;
}

Sort ApiTraceSolver::make_sort(const std::string name, uint64_t arity) const
{
  string sort_name = "s" + std::to_string(*sid);
  (*sid)++;
  trace_lines->push_back("Sort " + sort_name + " = s->make_sort(\"" + name
                         + "\", " + std::to_string(arity) + ");");
  Sort sort = sub_solver->make_sort(name, arity);
  (*sort2name)[(uintptr_t)sort->get()] = sort_name;
  return sort;
}

Sort ApiTraceSolver::make_sort(SortKind sk) const
{
  string sort_name = "s" + std::to_string(*sid);
  (*sid)++;
  trace_lines->push_back("Sort " + sort_name + " = s->make_sort("
                         + to_string(sk) + ");");
  Sort sort = sub_solver->make_sort(sk);
  (*sort2name)[(uintptr_t)sort->get()] = sort_name;
  return sort;
}

Sort ApiTraceSolver::make_sort(SortKind sk, uint64_t size) const
{
  string sort_name = "s" + std::to_string(*sid);
  (*sid)++;
  trace_lines->push_back("Sort " + sort_name + " = s->make_sort("
                         + to_string(sk) + ", " + to_string(size) + ");");
  Sort sort = sub_solver->make_sort(sk, size);
  (*sort2name)[(uintptr_t)sort->get()] = sort_name;
  return sort;
}

Sort ApiTraceSolver::make_sort(SortKind sk, const Sort & sort1) const
{
  string sort_name = "s" + std::to_string(*sid);
  (*sid)++;
  trace_lines->push_back("Sort " + sort_name + " = s->make_sort("
                         + to_string(sk) + ", "
                         + sort2name->at((uintptr_t)sort1->get()) + ");");
  Sort sort = sub_solver->make_sort(sk, sort1);
  (*sort2name)[(uintptr_t)sort->get()] = sort_name;
  return sort;
}

Sort ApiTraceSolver::make_sort(SortKind sk,
                               const Sort & sort1,
                               const Sort & sort2) const
{
  string sort_name = "s" + std::to_string(*sid);
  (*sid)++;
  trace_lines->push_back("Sort " + sort_name + " = s->make_sort("
                         + to_string(sk) + ", "
                         + sort2name->at((uintptr_t)sort1->get()) + ", "
                         + sort2name->at((uintptr_t)sort2->get()) + ");");
  Sort sort = sub_solver->make_sort(sk, sort1, sort2);
  (*sort2name)[(uintptr_t)sort->get()] = sort_name;
  return sort;
}

Sort ApiTraceSolver::make_sort(SortKind sk,
                               const Sort & sort1,
                               const Sort & sort2,
                               const Sort & sort3) const
{
  string sort_name = "s" + std::to_string(*sid);
  (*sid)++;
  trace_lines->push_back("Sort " + sort_name + " = s->make_sort("
                         + to_string(sk) + ", "
                         + sort2name->at((uintptr_t)sort1->get()) + ", "
                         + sort2name->at((uintptr_t)sort2->get()) + ", "
                         + sort2name->at((uintptr_t)sort3->get()) + ");");
  Sort sort = sub_solver->make_sort(sk, sort1, sort2, sort3);
  (*sort2name)[(uintptr_t)sort->get()] = sort_name;
  return sort;
}

Sort ApiTraceSolver::make_sort(SortKind sk, const SortVec & sorts) const
{
  string sort_name = "s" + std::to_string(*sid);
  (*sid)++;
  string vec_input = "{";
  for (auto s : sorts)
  {
    vec_input += sort2name->at((uintptr_t)s->get()) + ", ";
  }
  vec_input += "}";
  trace_lines->push_back("Sort " + sort_name + " = s->make_sort(" + vec_input
                         + ");");
  Sort sort = sub_solver->make_sort(sk, sorts);
  (*sort2name)[(uintptr_t)sort->get()] = sort_name;
  return sort;
}

Term ApiTraceSolver::make_term(bool b) const
{
  string term_name = "n" + std::to_string(*nid);
  (*nid)++;
  trace_lines->push_back("Term " + term_name + " = s->make_term("
                         + std::to_string(b) + ");");
  Term term = sub_solver->make_term(b);
  (*term2name)[(uintptr_t)term->get()] = term_name;
  return term;
}

Term ApiTraceSolver::make_term(int64_t i, const Sort & sort) const
{
  string term_name = "n" + std::to_string(*nid);
  (*nid)++;
  trace_lines->push_back("Term " + term_name + " = s->make_term("
                         + std::to_string(i) + ", "
                         + sort2name->at((uintptr_t)sort->get()) + ");");
  Term term = sub_solver->make_term(i, sort);
  (*term2name)[(uintptr_t)term->get()] = term_name;
  return term;
}

Term ApiTraceSolver::make_term(const std::string val,
                               const Sort & sort,
                               uint64_t base = 10) const
{
  string term_name = "n" + std::to_string(*nid);
  (*nid)++;
  trace_lines->push_back("Term " + term_name + " = s->make_term(\"" + val
                         + "\", " + sort2name->at((uintptr_t)sort->get())
                         + std::to_string(base) + ");");
  Term term = sub_solver->make_term(val, sort, base);
  (*term2name)[(uintptr_t)term->get()] = term_name;
  return term;
}

Term ApiTraceSolver::make_term(const Term & val, const Sort & sort) const
{
  string term_name = "n" + std::to_string(*nid);
  (*nid)++;
  trace_lines->push_back("Term " + term_name + " = s->make_term("
                         + term2name->at((uintptr_t)val->get()) + ", "
                         + sort2name->at((uintptr_t)sort->get()) + ");");
  Term term = sub_solver->make_term(val, sort);
  (*term2name)[(uintptr_t)term->get()] = term_name;
  return term;
}

Term ApiTraceSolver::make_symbol(const std::string name, const Sort & sort)
{
  string term_name = "n" + std::to_string(*nid);
  (*nid)++;
  trace_lines->push_back("Term " + term_name + " = s->make_symbol(\"" + name
                         + "\", " + sort2name->at((uintptr_t)sort->get())
                         + ");");
  Term term = sub_solver->make_symbol(name, sort);
  (*term2name)[(uintptr_t)term->get()] = term_name;
  return term;
}

Term ApiTraceSolver::make_term(Op op, const Term & t) const
{
  string term_name = "n" + std::to_string(*nid);
  (*nid)++;
  trace_lines->push_back("Term " + term_name + " = s->make_term("
                         + op_to_api_str(op) + ", "
                         + term2name->at((uintptr_t)t->get()) + ");");
  Term term = sub_solver->make_term(op, t);
  (*term2name)[(uintptr_t)term->get()] = term_name;
  return term;
}

Term ApiTraceSolver::make_term(Op op, const Term & t0, const Term & t1) const
{
  string term_name = "n" + std::to_string(*nid);
  (*nid)++;
  trace_lines->push_back("Term " + term_name + " = s->make_term("
                         + op_to_api_str(op) + ", "
                         + term2name->at((uintptr_t)t0->get()) + ", "
                         + term2name->at((uintptr_t)t1->get()) + ");");
  Term term = sub_solver->make_term(op, t0, t1);
  (*term2name)[(uintptr_t)term->get()] = term_name;
  return term;
}

Term ApiTraceSolver::make_term(Op op,
                               const Term & t0,
                               const Term & t1,
                               const Term & t2) const
{
  string term_name = "n" + std::to_string(*nid);
  (*nid)++;
  trace_lines->push_back("Term " + term_name + " = s->make_term("
                         + op_to_api_str(op) + ", "
                         + term2name->at((uintptr_t)t0->get()) + ", "
                         + term2name->at((uintptr_t)t1->get()) + ", "
                         + term2name->at((uintptr_t)t2->get()) + ");");
  Term term = sub_solver->make_term(op, t0, t1);
  (*term2name)[(uintptr_t)term->get()] = term_name;
  return term;
}

void ApiTraceSolver::reset()
{
  trace_lines.push_back("s->reset();");
  sub_solver->reset();
}

void ApiTraceSolver::reset_assertions()
{
  trace_lines.push_back("s->reset_assertions();");
  sub_solver->reset_assertions();
}

Term ApiTraceSolver::substitute(const Term term,
                                const UnorderedTermMap & substitution_map) const
{
  unordered_map<string, string> str_subst_map;
  trace_lines->push_back("unordered_map<Term, Term> subst;");
  for (auto elem : substitution_map)
  {
    trace_lines->push_back(
        "subst[" + term2name->at((uintptr_t)elem.first->get())
        + "] = " + term2name->at((uintptr_t)elem.second->get()) + ";");
  }

  string term_name = "n" + std::to_string(*nid);
  (*nid)++;

  trace_lines->push_back("Term " + term_name + " = s->substitute("
                         + term2name->at((uintptr_t)term->get()) + ", subst);");

  Term res = sub_solver->substitute(term, substitution_map);
  (*term2name)[(uintptr_t)res->get()] = term_name;
  return res;
}

void dump_smt2(std::string filename) const
{
  trace_lines->push_back("s->dump_smt2(\"" + filename + "\");");
  sub_solver->dump_smt2(filename);
}

void dump_api_trace(std::string filename)
{
  ofstream f;
  f.open(filename);
  f << "#include \"smt-switch/smt.h\"\n";
  f << "//include your chosen solver here\n";
  f << "\n\nusing namespace smt;\nusingnamespace std;\n\n";
  f << "int main() {";
  for (auto line : trace_lines)
  {
    f << "  " << line << "\n";
  }
  f << "}";
  f.close();
}

}  // namespace smt
