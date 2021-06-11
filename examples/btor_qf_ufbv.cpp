#include <iostream>
#include <map>
#include "smt-switch/boolector_factory.h"
#include "smt-switch/smt.h"
using namespace smt;
using namespace std;


void cnf_to_dimacs(Term cnf){
	 TermVec vecs({cnf});
	 TermVec vecs2;
	 //to separate the clauses
	 while(!vecs.empty()){
	 		Term t=vecs.back();
	 		vecs.pop_back();
	 		smt::Op op=t->get_op();
	 		if(op.prim_op==smt::And){
	 			for(auto u:t){
	 				vecs.push_back(u);
	 			}
	 		}
	 		else{
	 			vecs2.push_back(t);
	 		}
	 }
	 //To store the literals from each clause
	 vector<vector<Term>>literals;

	 map<string, int>ma;
	 int ptr=0;

	 for(auto u:vecs2){
	 	vector<Term>add;
	 	vector<Term>le({u});
	 	while(!le.empty()){
	 		Term t=le.back();
	 		le.pop_back();
	 		smt::Op op=t->get_op();
	 		if(op.prim_op==smt::Or){
	 			for(auto u:t){
	 				le.push_back(u);
	 			}
	 		}
	 		else{
	 			add.push_back(t);
	 		}
	 	}
	 	literals.push_back(add);
	 }

 	
	 //Mapping the symbols to natural numbers
	 for(auto u:literals){
	 	for(auto uu:u){
	 		if(uu->is_symbolic_const()){
	 			if(ma.find(uu->to_string())==ma.end()){
	 				ma[uu->to_string()]=ptr;
	 				ptr++;
	 			}
	 		}
	 		else{
	 			Term t=(*(uu->begin()));
	 			if(ma.find(t->to_string())==ma.end()){
	 				ma[t->to_string()]=ptr;
	 				ptr++;
	 			}
	 		}
	 	}
	 }
	 //printing the output in DIMACS format
	 cout<<"p cnf ";
	 cout<<ptr<<" ";
	 int sz=literals.size();
	 cout<<sz<<endl;
	 
	for(auto u:literals){
		for(auto uu:u){
			if(uu->is_symbolic_const()){
				cout<<ma[uu->to_string()]+1<<" ";
			}
			else{
				Term t=(*(uu->begin()));
				cout<<(-(ma[t->to_string()]+1))<<" ";
			}
		}
		cout<<0<<endl;
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
 Sort boolsort=s->make_sort(BOOL);
 Term a = s->make_symbol("a", boolsort);
 Term b = s->make_symbol("b", boolsort);
 Term c = s->make_symbol("c", boolsort);
 Term d = s->make_symbol("d", boolsort);
 Term clause1 = s->make_term(Or, a, s->make_term(Or, b, s->make_term(Not, c)));
 Term clause2 = s->make_term(Or, b, s->make_term(Or, s->make_term(Not, c), d));
 Term clause3 = s->make_term(Or, d, s->make_term(Or, s->make_term(Not, c), a));
 Term cnf=s->make_term(And, clause1, s->make_term(And, clause2, clause3));
 


 cnf_to_dimacs(cnf);
 



 // for(auto u:literals){
 // 	for(auto uu:u){

 // 	}
 // }



  

//  Sort bvs = s->make_sort(BV, 32);
//  Sort funs =
//    s->make_sort(FUNCTION, {bvs, bvs});

//  Term x = s->make_symbol("x", bvs);
//  Term y = s->make_symbol("y", bvs);
//  Term f = s->make_symbol("f", funs);

//  Op ext = Op(Extract, 15, 0);
//  Term x0 = s->make_term(ext, x);
//  Term y0 = s->make_term(ext, y);

//  Term fx = s->make_term(Apply, f, x);
//  Term fy = s->make_term(Apply, f, y);
//  s->assert_formula(
//    s->make_term(Distinct, fx, fy));
//   s->push(1);
//  s->assert_formula(
//    s->make_term(Equal, x0, y0));
//  cout <<  s->check_sat() << endl;

//  cout << s->get_value(x) << endl;
//  s->pop(1);

//  Term xy = s->make_term(BVAnd, x, y);
//  Term a1 = s->make_term(BVUge, x0, y0);
//  Term a2 = s->make_term(BVUge, xy, x);
//  Term a3 = s->make_term(BVUge, xy, y);
//  cout <<
//    s->check_sat_assuming({a1, a2, a3})
//    << endl;
//  UnorderedTermSet ua;
//  s->get_unsat_assumptions(ua);
//  for (Term t : ua) { cout << t << endl; }
// }
}
