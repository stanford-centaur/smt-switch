#include <iostream>
#include <map>
#include <sstream>
#include "smt-switch/boolector_factory.h"
#include "smt-switch/smt.h"
using namespace smt;
using namespace std;



void cnf_to_dimacs(Term cnf, std::ostringstream & y)
{
  Sort sort = cnf->get_sort();
  assert(sort->get_sort_kind() == BOOL);
  if (cnf->is_value() && cnf->to_string() == "true")
  {  // empty cnf formula
    y << "p cnf 0 0\n";
    return;
  }
  TermVec before_and_elimination({ cnf });
  TermVec after_and_elimination;
  // This while loop separate the clauses, after_and_elimination will contain
  // all clauses because every smt::and op will be eliminated. This happens
  // because until smt::and op is not detected that term is added back to
  // before_and_elimination, and as no term with smt::or as the primOp is
  // touched all clauses shall be separated and be intact
  while (!before_and_elimination.empty())
  {
    Term t = before_and_elimination.back();
    before_and_elimination.pop_back();
    smt::Op op = t->get_op();
    
    assert(op.is_null() || op == smt::Or || op == smt::And || op == smt::Not);
    if (op.prim_op == smt::And)
    {
      for (auto u : t)
      {
        before_and_elimination.push_back(u);
      }
    }
    else
    {
      after_and_elimination.push_back(t);
    }
  }
  // Storing literals from each clause, each vector in clauses will contain the
  // literals from a clause
  vector<vector<Term>> clauses;

  for (auto u : after_and_elimination)
  {
    vector<Term> after_or_elimination;
    vector<Term> before_or_elimination({ u });
    while (!before_or_elimination.empty())
    {  // This while loop functions in the same way as above and eliminates
       // smt::or by separating the literals
      Term t = before_or_elimination.back();
      before_or_elimination.pop_back();
      smt::Op op = t->get_op();
      
      assert(op.is_null() || op == smt::Or || op == smt::Not);
      
      if(op.prim_op == smt::Or)
      {
        for(auto u : t)
        {
          before_or_elimination.push_back(u);
        }
      }
      else
      {
        assert(op.is_null() || op == smt::Not);
        after_or_elimination.push_back(t);
      }
    }
    clauses.push_back(after_or_elimination);
   }

   map<Term, int> ma;  // This map will create a mapping from symbols to
                            // distinct contiguous integer values.
   int ptr = 0;  // pointer to store the next integer used in mapping
   //iterating within each clause and mapping every distinct symbol to a natural number
   for (auto u : clauses)
   {
     for (auto uu : u)
     {  // Using literals from all the clauses to create the mapping
       if (uu->is_value() && uu->to_string() == "false")
       {  // For an empty clause, which will just contain the term "false"
       }
       else if (uu->is_symbolic_const())
       {  // A positive literal
         if (ma.find(uu) == ma.end())
         {  // Checking if symbol is absent in the mapping done till now
           ptr++;
           ma[uu] = ptr;
         }
       }
       else
       {  // A negative literal
         Term t = (*(uu->begin()));
         if (ma.find(t) == ma.end())
         {
           ptr++;
           ma[t] = ptr;
         }
       }
     }
   }
   //printing the output in DIMACS format
   y << "p cnf ";
   y << ptr;  // number of distinct symbols
   y << " ";

   int sz = clauses.size();

   y << sz;  // number of clauses
   y << "\n";

   //iterating within each clause and assigning the literal their mapped value(for a positive literal) or it's negative value(for a negative literal)
   for (auto u : clauses)
   {
     for (auto uu : u)
     {
       if (uu->is_value() && uu->to_string() == "false")
       {  // For an empty clause
       }
       else if (uu->is_symbolic_const())
       {
         y << (ma[uu]);  // Positive number for a positive literal
         y << " ";
       }
       else
       {
         Term t = (*(uu->begin()));
         y << ((-(ma[t])));  // Negative number for a negative literal
         y << " ";
       }
     }
     y << 0;  // Symbolizing end of line
     y << "\n";
  }
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
 s->set_opt("produce-unsat-assumptions",
   "true");
  Sort boolsort = s->make_sort(BOOL);
  Term a = s->make_symbol("a", boolsort);
  Term b = s->make_symbol("b", boolsort);
  Term c = s->make_symbol("c", boolsort);
  Term d = s->make_symbol("d", boolsort);
  Term clause1 = s->make_term(Or, a, s->make_term(Or, b, s->make_term(Not, c)));
  Term clause2 = s->make_term(Or, b, s->make_term(Or, s->make_term(Not, c), d));
  Term clause3 = s->make_term(Or, d, s->make_term(Or, s->make_term(Not, c), a));
  Term cnf=s->make_term(And, clause1, s->make_term(And, clause2, clause3));
//The terms in the output string is not in accordance with the order of the input because of how to function is operating on the terms
//, a dry run will show how the mapping of symbol to integer happens

  // Test 1

  ostringstream y;
  cnf_to_dimacs(cnf, y);  // cnf = ((a v b v ~c) /\ (b v ~c v d) /\ (d v ~c v
                          // a))
  string ret = y.str();
  string ans = "p cnf 4 3\n1 -2 3 0\n3 -2 4 0\n-2 4 1 0\n";
  cout<<ret<<endl<<ans<<endl;
}
