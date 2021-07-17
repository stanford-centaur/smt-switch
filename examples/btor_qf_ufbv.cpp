#include <iostream>
#include <map>

#include "smt-switch/boolector_factory.h"
#include "smt-switch/identity_walker.h"
#include "smt-switch/smt.h"
using namespace smt;
using namespace std;

// mapping each subformula with a new name and returning a vector of pair of
// terms. Each pair consists of the parent term and it's children(for each
// subformula)
class TseitinTraversal : public IdentityWalker
{
 public:
  std::vector<std::pair<Term, Term>>
      reduced;  // stores a pair of (lhs, rhs) in x1(lhs)<->(formula(rhs))

  TseitinTraversal(SmtSolver solver_) : IdentityWalker{ solver_, false } {}
  WalkerStepResult visit_term(Term & term)
  {
    Sort boolsort = term->get_sort();
    assert(term->get_sort() == boolsort);

    auto give_symbolic_name = [&](Term t) {  // producing a new symbol
      int pt = 1;
      while (true)
      {
        try
        {
          return solver_->make_symbol("cnf_formula_new_" + to_string(pt), boolsort);
        }
        catch (IncorrectUsageException & e)
        {
          pt++;
        }
      }

    };
    if (!preorder_)  // using post order traversal as I need the new names of
                     // the children to generate the new term
    {
      smt::Op op = term->get_op();
      if (!op.is_null())
      {
        vector<Term> vec;  // a vector of all children
        for (auto u : term)
        {
          Term term_name;
          bool present = query_cache(
              u,
              term_name);  // finding the new name of each child from the cache
          assert(present == true);
          vec.push_back(term_name);
        }
        Term term_name;
        query_cache(term, term_name);

        term_name = give_symbolic_name(term);  // making a new symbol
        save_in_cache(term, term_name);

        reduced.push_back({ term_name, solver_->make_term(op, vec) });
      }
      else
      {  // mapping a symbolic constant to itself
        save_in_cache(term, term);
      }
    }

    return Walker_Continue;
  }
};

// binarising xor with multiple children
class XorBinarize : public IdentityWalker
{
 public:
  XorBinarize(SmtSolver solver_) : IdentityWalker{ solver_, false } {}
  WalkerStepResult visit_term(Term & term)
  {
    if (!preorder_)
    {
      smt::Op op = term->get_op();
      if (!op.is_null())
      {
        if (op == smt::Xor)
        {
          auto it = term->begin();
          Term term_name;
          query_cache((*it),
                      term_name);  // finding the mapped term from the cache
          Term ne = term_name;
          it++;
          while (it != term->end())
          {  // Binarising the term
            Term term_name;
            query_cache((*it), term_name);
            ne = solver_->make_term(op, ne, term_name);
            it++;
          }
          save_in_cache(term, ne);  // storing the new binarised term in cache
        }
        else
        {
          save_in_cache(term, term);
        }
      }
      else
      {
        save_in_cache(term, term);
      }
    }

    return Walker_Continue;
  }
  Term acc_cache(Term term)
  {
    Term ne;
    query_cache(term, ne);
    return ne;
  }
};

Term to_cnf(Term formula, SmtSolver s)
{
  Sort boolsort = formula->get_sort();
  assert(formula->get_sort() == boolsort);
  if (formula->is_symbolic_const())
  {
    return formula;
  }
  XorBinarize bin(s);
  bin.visit(formula);  // binarising the formula
  Term formula2 = bin.acc_cache(formula);
  TseitinTraversal obj(s);
  obj.visit(
      formula2);  // traversing the binarised formula to create of pairs of
                  // (c<->(a op b)) which will be used in the transformation

  Term parent = obj.reduced.back().first;

  TermVec clauses;

  // the vector of pairs reduced contains pairs in the form of (c)<->(a op b),
  // where c is the first term of the pair and (a op b) is the second
  for (auto u : obj.reduced)
  {
    Term fi = u.first;
    Term se = u.second;
    smt::Op op = se->get_op();

    if (op == smt::Or)
    {  //(c<->Or(x1, x2, x3, x4....)) = (Or(~c, x1, x2, x3, x4) And (And((c or
       //~x1), (c or ~x2), (c or ~x3), (c or ~x4))
      vector<Term> vec;
      vector<Term> vec2;
      vec.push_back(s->make_term(Not, fi));
      for (auto u : se)
      {
        vec.push_back(u);
        vec2.push_back(s->make_term(Or, fi, s->make_term(Not, u)));
      }
      clauses.push_back(s->make_term(Or, vec));
      clauses.push_back(s->make_term(And, vec2));
    }
    else if (op == smt::And)
    {  //(c<->And(x1, x2, x3, x4....)) = (Or(c, ~x1, ~x2, ~x3, ~x4) And (And((~c
       //or x1), (~c or x2), (~c or x3), (~c or x4))
      vector<Term> vec;
      vector<Term> vec2;
      vec.push_back(fi);
      for (auto u : se)
      {
        vec.push_back(s->make_term(Not, u));
        vec2.push_back(s->make_term(Or, u, s->make_term(Not, fi)));
      }
      clauses.push_back(s->make_term(Or, vec));
      clauses.push_back(s->make_term(And, vec2));
    }
    else if (op == smt::Xor)
    {  //((~a) v (~b) v (~c)) and ((a) v (b) v (~c)) and ((c) v (b) v (~a)) and
       //((c) v (a) v (~b))
      auto it = (se->begin());
      Term le = (*it);
      it++;
      Term ri = (*it);
      clauses.push_back(s->make_term(
          Or,
          s->make_term(Or, s->make_term(Not, le), s->make_term(Not, ri)),
          s->make_term(Not, fi)));
      clauses.push_back(
          s->make_term(Or, s->make_term(Or, le, ri), s->make_term(Not, fi)));
      clauses.push_back(
          s->make_term(Or, s->make_term(Or, fi, ri), s->make_term(Not, le)));
      clauses.push_back(
          s->make_term(Or, s->make_term(Or, fi, le), s->make_term(Not, ri)));
    }
    else if (op == smt::Implies)
    {  //((~a) v (b) v (~c)) and ((a) v (c)) and ((~b) v (c))
      auto it = (se->begin());
      Term le = (*it);
      it++;
      Term ri = (*it);
      clauses.push_back(
          s->make_term(Or,
                       s->make_term(Or, s->make_term(Not, le), ri),
                       s->make_term(Not, fi)));
      clauses.push_back(s->make_term(Or, le, fi));
      clauses.push_back(s->make_term(Or, s->make_term(Not, ri), fi));
    }
    else if (op == smt::Equal)
    {  //((~a) v (~b) v (c)) and ((a) v (b) v (c)) and ((~c) v (~b) v (a)) and
       //((c) v (~a) v (b))
      auto it = (se->begin());
      Term le = (*it);
      it++;
      Term ri = (*it);
      clauses.push_back(s->make_term(
          Or,
          s->make_term(Or, s->make_term(Not, le), s->make_term(Not, ri)),
          fi));
      clauses.push_back(s->make_term(Or, s->make_term(Or, le, ri), fi));
      clauses.push_back(
          s->make_term(Or,
                       s->make_term(Or, le, s->make_term(Not, ri)),
                       s->make_term(Not, fi)));
      clauses.push_back(
          s->make_term(Or,
                       s->make_term(Or, s->make_term(Not, le), ri),
                       s->make_term(Not, fi)));
    }
    else
    {  //((~a) v (~c)) and ((a) v (c))
      Term le = (*(se->begin()));
      clauses.push_back(
          s->make_term(Or, s->make_term(Not, le), s->make_term(Not, fi)));
      clauses.push_back(s->make_term(Or, le, fi));
    }
  }
  // taking the and of all clauses generated to create the cnf
  Term ret = s->make_term(And, clauses);
  ret = s->make_term(And, parent, ret);

  return ret;
}

int main()
{
 // Boolector aliases booleans and bitvectors of size one
 // and also performs on-the-fly rewriting
 // if you'd like to maintain the term structure, you can
 // enable logging by passing true
 SmtSolver s = BoolectorSolverFactory::create(true);

 s->set_logic("QF_UFBV");
 s->set_opt("incremental", "true");
 s->set_opt("produce-models", "true");
 s->set_opt("produce-unsat-assumptions", "true");
 Sort boolsort = s->make_sort(BOOL);
 Term p = s->make_symbol("p", boolsort);
 Term q = s->make_symbol("q", boolsort);
 Term r = s->make_symbol("r", boolsort);
 Term t = s->make_symbol("t", boolsort);

 //a=((p or q) and r) implies (not t)
  Term a = s->make_term(Implies, s->make_term(And, s->make_term(Or, p, q), r), s->make_term(Not, t));
  Term cnf1 = to_cnf(a, s);
  cout<<cnf1->to_string()<<endl;
  //b=(not (p xor q))
  Term b = s->make_term(Not, s->make_term(Xor, p, q));
  Term cnf2 = to_cnf(b, s);
  cout<<cnf2->to_string()<<endl;
  //c=((not p) and p)
  Term c = s->make_term(And, s->make_term(Not, p), p);
  Term cnf3 = to_cnf(c, s);
  cout<<cnf3->to_string()<<endl;


 // cout<<cnf1<<endl;
}
