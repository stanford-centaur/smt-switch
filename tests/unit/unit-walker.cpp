/*********************                                                        */
/*! \file unit-walker.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Unit tests for term walkers.
**
**
**/

#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "identity_walker.h"
#include "smt.h"
#include "tree_walker.h"

using namespace smt;
using namespace std;

namespace smt_tests {

  //TODO is this even being used, why is it here and why just return
class DummyTreeWalker : TreeWalker {
  TreeWalkerStepResult visit_term(smt::Term & formula, smt::Term & term, std::vector<int> & path) override{
    return TreeWalker_Continue;
  }
};

class UnitWalkerTests : public ::testing::Test,
                        public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());

    bvsort = s->make_sort(BV, 4);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort });
    arrsort = s->make_sort(ARRAY, bvsort, bvsort);
    boolsort = s->make_sort(BOOL);
  }
  SmtSolver s;
  Sort bvsort, funsort, arrsort, boolsort;
};

class FreshTreeWalker : public TreeWalker {
  int b_iter {};

  using TreeWalker::TreeWalker;

//  FreshTreeWalker(const smt::SmtSolver & solver,
  //               bool clear_cache,
    //             smt::UnorderedTermPairMap * ext_cache = nullptr)
      //: solver_(solver), clear_cache_(clear_cache), ext_cache_(ext_cache){};

  TreeWalkerStepResult visit_term(smt::Term & formula, smt::Term & term, std::vector<int> & path) override{

    Sort boolsort = solver_->make_sort(BOOL);

    string var_name = string("b") + to_string(b_iter);
    Term b = solver_->make_symbol(var_name, boolsort);
    b_iter++;

    Op op = term->get_op();
    if (!op.is_null())
    {
      TermVec cached_children;
      Term c;
      pair <Term, vector<int>> occurrence;
      for (auto t : term)
      {
       // occurrence.first = t;
        //occurrence.second = path;
        //query_cache(t, occurrence);
        cached_children.push_back(t); //TODO this needs to be only first part of pair (the term)
      }
      pair <Term, vector<int>> occ;
      occ.first = formula;
      occ.second = path;
      Term occ_key;
      occ_key = solver_->make_term(op, cached_children);
      save_in_cache(b, occ);
    }
    else
    {
      pair <Term, vector<int>> occ;
      occ.first = formula;
      occ.second = path;
      save_in_cache(b, occ);
    }
    return TreeWalker_Continue;
  }
};


TEST_P(UnitWalkerTests, Simple)
{
  Term x = s->make_symbol("x", bvsort);
  Term xp1 = s->make_term(BVAdd, x, s->make_term(1, bvsort));
  IdentityWalker iw(s, false);
  EXPECT_EQ(xp1, iw.visit(xp1));
  // visit a second time
  EXPECT_EQ(xp1, iw.visit(xp1));
}

TEST_P(UnitWalkerTests, SimpleSubstitution)
{
  // using IdentityWalker for substitution
  // no reason to use this over the substitute method
  // only for testing

  Term x = s->make_symbol("x", bvsort);
  Term xp1 = s->make_term(BVAdd, x, s->make_term(1, bvsort));

  Term y = s->make_symbol("y", bvsort);
  Term yp1 = s->make_term(BVAdd, y, s->make_term(1, bvsort));

  UnorderedTermMap subs({ { x, y } });
  IdentityWalker iw(s, false, &subs);
  EXPECT_EQ(yp1, iw.visit(xp1));
  // visit a second time
  EXPECT_EQ(yp1, iw.visit(xp1));
  EXPECT_EQ(subs.size(), 3);  // should contain, x, 1, and x+1
}

TEST_P(UnitWalkerTests, ArraySubstitution)
{
  // using IdentityWalker for substitution
  // no reason to use this over the substitute method
  // only for testing

  Term x = s->make_symbol("x", bvsort);
  Term arr = s->make_symbol("arr", arrsort);
  Term arrx = s->make_term(Select, arr, x);

  Term x_0 = s->make_symbol("x@0", bvsort);
  Term arr_0 = s->make_symbol("arr@0", arrsort);
  Term arrx_0 = s->make_term(Select, arr_0, x_0);

  UnorderedTermMap subs({ { x, x_0 }, { arr, arr_0 } });
  IdentityWalker iw(s, false, &subs);
  EXPECT_EQ(arrx_0, iw.visit(arrx));
  // visit a second time
  EXPECT_EQ(arrx_0, iw.visit(arrx));
}

TEST_P(UnitWalkerTests, FunSubstitution)
{
  // using IdentityWalker for substitution
  // no reason to use this over the substitute method
  // only for testing

  Term f = s->make_symbol("f", funsort);

  Term x = s->make_symbol("x", bvsort);
  Term fx = s->make_term(Apply, f, x);

  Term y = s->make_symbol("y", bvsort);
  Term fy = s->make_term(Apply, f, y);

  UnorderedTermMap subs({ { x, y } });
  IdentityWalker iw(s, false, &subs);
  EXPECT_EQ(fy, iw.visit(fx));
  // visit a second time
  EXPECT_EQ(fy, iw.visit(fx));
}

void printVector(vector<int> v){
  for (int i:v){
    cout << v[i] << ", " << endl;
  }
}

string vectorToString(vector<int> v){
  string s;
  for (int i:v){
    s += to_string(i);
    s += ", ";
  }
  return s;
}


void printMap(UnorderedTermPairMap const &m){
  for (auto const& pair : m){
    auto val_pair = pair.second;
    cout << pair.first << ": " << "<" << val_pair.first << ", (" << vectorToString(val_pair.second) << ")>" << " }\n";
    //cout << "{ " << pair.first << ": " << pair.second << " }" << endl;
  }
}

TEST_P(UnitWalkerTests, SimpleTree)
{
  SolverConfiguration sc = GetParam();
  if (sc.is_logging_solver) {

  Term x = s->make_symbol("x", bvsort);
  Term xp1 = s->make_term(BVAdd, x, s->make_term(1, bvsort));

  UnorderedTermPairMap UndMap;
  TreeWalker iw(s, false, &UndMap);

  pair <Term, vector<int>> p1;
  p1 = iw.visit(xp1);
  Term xp11 = p1.first;
  EXPECT_EQ(xp1, xp11);
  // visit a second time
//  printMap(UndMap);
  EXPECT_EQ(xp1, xp11);

  map<Term, pair<Term, vector<int>>> expected_map;
  pair <Term, vector<int>> n0;
  n0.first = xp1;
  vector<int> n0path;
  n0.second = n0path;
  expected_map[xp1] = n0;
  pair <Term, vector<int>> n1;
  n1.first = xp1;
  vector<int> n1path = {0};
  n1.second = n1path;
  expected_map[x] = n1;
  pair <Term, vector<int>> n2;
  n2.first = xp1;
  vector<int> n2path = {1};
  n2.second = n2path;
  expected_map[s->make_term(1, bvsort)] = n2;

  for (auto const& x : UndMap){
//    EXPECT_EQ(x.first, expected_map[x.first]);
    EXPECT_EQ(x.second.first, expected_map[x.first].first); //testing equivalence of first element in pair: the topmost node
//    EXPECT_EQ(x.second.second, expected_map[x.first].second); //testing equivalence of 2nd element in pair: the path
    ASSERT_EQ(x.second.second.size(), expected_map[x.first].second.size());
    for (int i = 0; i < x.second.second.size(); i++){
//      cout << "size: " << x.second.second.size() << endl;
 //     cout <<  x.second.second[i]<< endl;
   //   cout <<  expected_map[x.first].second[i]<< endl;
      EXPECT_EQ(x.second.second[i], expected_map[x.first].second[i]);
    }
    }
  }
}

TEST_P(UnitWalkerTests, PathDecomp)
{
  SolverConfiguration sc = GetParam();
  if (sc.is_logging_solver) {
  Term x = s->make_symbol("x", bvsort);
  Term y = s->make_symbol("y", bvsort);
  Term xp1 = s->make_term(BVAdd, x, s->make_term(1, bvsort));
  Term xp1py = s->make_term(BVAdd, xp1, y); //diff than if had done ADD(x, 1, y) ?
  Term yexp1py = s->make_term(Equal, y, xp1py);

  map<Term, pair<Term, vector<int>>> expected_map;
  //y = x+1+y
  pair <Term, vector<int>> n0;
  n0.first = yexp1py;
  vector<int> n0path;
  n0.second = n0path;
  expected_map[yexp1py] = n0;
  //y: {0}
  pair <Term, vector<int>> n3;
  n3.first = yexp1py;
  vector<int> n3path = {0};
  n3.second = n3path;
  expected_map[y] = n3;
  //x+1+y: {1}
  pair <Term, vector<int>> n1;
  n1.first = yexp1py;
  vector<int> n1path = {1};
  n1.second = n1path;
  expected_map[xp1py] = n1;
  //x+1: {1,0}
  pair <Term, vector<int>> n2;
  n2.first = yexp1py;
  vector<int> n2path = {1, 0};
  n2.second = n2path;
  expected_map[xp1] = n2;
  //y: {1,1} (gets overwritten)
  //x: {1,0,0}
  pair <Term, vector<int>> n4;
  n4.first = yexp1py;
  vector<int> n4path = {1, 0, 0};
  n4.second = n4path;
  expected_map[x] = n4;
  //1: {1,0,1}
  pair <Term, vector<int>> n5;
  n5.first = yexp1py; //should be type term...
  vector<int> n5path = {1, 0, 1};
  n5.second = n5path;
  expected_map[s->make_term(1, bvsort)] = n5; //does this need to be turned into a term somehow?

  UnorderedTermPairMap UndMap;
  TreeWalker iw(s, false, &UndMap);

  pair <Term, vector<int>> p1;
  p1 = iw.visit(yexp1py);
//  Term xp11 = p1.first;
//  EXPECT_EQ(yexp1py, xp11);
//  cout << s->get_solver_enum() << endl;
//  SolverConfiguration sc = GetParam();
//  cout << sc.is_logging_solver << std::endl;

//  printMap(UndMap);

  for (auto const& x : UndMap){
    EXPECT_EQ(x.second.first, expected_map[x.first].first); //testing equivalence of first element in pair: the topmost node
    ASSERT_EQ(x.second.second.size(), expected_map[x.first].second.size());
    for (int i = 0; i < x.second.second.size(); i++){ //testing equivalence of second element in pair (path) by looping through vector of ints
      EXPECT_EQ(x.second.second[i], expected_map[x.first].second[i]);
    }
    }
  }
}

TEST_P(UnitWalkerTests, PathTests1)
{
  //testing repeated values
  SolverConfiguration sc = GetParam();
  if (sc.is_logging_solver) {
  Term x = s->make_symbol("x", bvsort);
  Term y = s->make_symbol("y", bvsort);
  Term xpx = s->make_term(BVAdd, x, x);
  Term ypy = s->make_term(BVAdd, y, y);
  Term xp2 = s->make_term(BVAdd, x, s->make_term(2, bvsort));
  Term lmt = s->make_term(BVSub, xp2, xpx);
  Term rhs = s->make_term(BVAdd, ypy, lmt);
  Term fullform = s->make_term(Equal, xpx, rhs);

  map<Term, pair<Term, vector<int>>> expected_map;
  //fullform: {}
  pair <Term, vector<int>> n0;
  n0.first = fullform;
  vector<int> n0path;
  n0.second = n0path;
  expected_map[fullform] = n0;
  //x+x: {0}
  pair <Term, vector<int>> n1;
  n1.first = fullform;
  vector<int> n1path = {0};
  n1.second = n1path;
  expected_map[xpx] = n1;
  //x: {0,0}
  pair <Term, vector<int>> n2;
  n2.first = fullform;
  vector<int> n2path = {0, 0};
  n2.second = n2path;
  expected_map[x] = n2;
  //(y+y)+(x+2)-(x+x): {1}
  pair <Term, vector<int>> n3;
  n3.first = fullform;
  vector<int> n3path = {1};
  n3.second = n3path;
  expected_map[rhs] = n3;
  //y+y: {1,0}
  pair <Term, vector<int>> n4;
  n4.first = fullform;
  vector<int> n4path = {1, 0};
  n4.second = n4path;
  expected_map[ypy] = n4;
  //y: {1,0,0}
  pair <Term, vector<int>> n5;
  n5.first = fullform;
  vector<int> n5path = {1, 0, 0};
  n5.second = n5path;
  expected_map[y] = n5;
  //x+2: {1,1,0}
  pair <Term, vector<int>> n6;
  n6.first = fullform;
  vector<int> n6path = {1, 1, 0};
  n6.second = n6path;
  expected_map[xp2] = n6;
  //2: {1,1,0,1}
  pair <Term, vector<int>> n7;
  n7.first = fullform;
  vector<int> n7path = {1, 1, 0, 1};
  n7.second = n7path;
  expected_map[s->make_term(2, bvsort)] = n7;
  //x+2-x+x: {1,1}
  pair <Term, vector<int>> n8;
  n8.first = fullform;
  vector<int> n8path = {1, 1};
  n8.second = n8path;
  expected_map[lmt] = n8;

  UnorderedTermPairMap UndMap;
  TreeWalker iw(s, false, &UndMap);

  pair <Term, vector<int>> p1;
  p1 = iw.visit(fullform);
//  Term = p1.first;

//  printMap(UndMap);

  for (auto const& x : UndMap){
    EXPECT_EQ(x.second.first, expected_map[x.first].first); //testing equivalence of first element in pair: the topmost node
    ASSERT_EQ(x.second.second.size(), expected_map[x.first].second.size());
    for (int i = 0; i < x.second.second.size(); i++){
      EXPECT_EQ(x.second.second[i], expected_map[x.first].second[i]);
    }
    }
  }
}

TEST_P(UnitWalkerTests, PathTests2)
{
  SolverConfiguration sc = GetParam();
  if (sc.is_logging_solver) {

  Term x = s->make_symbol("x", bvsort);

  UnorderedTermPairMap UndMap;
  TreeWalker iw(s, false, &UndMap);

  pair <Term, vector<int>> p1;
  p1 = iw.visit(x);

  map<Term, pair<Term, vector<int>>> expected_map;
  pair <Term, vector<int>> n0;
  n0.first = x;
  vector<int> n0path;
  n0.second = n0path;
  expected_map[x] = n0;

  //printMap(UndMap);

  for (auto const& x : UndMap){
    EXPECT_EQ(x.second.first, expected_map[x.first].first); //testing equivalence of first element in pair: the topmost node
    ASSERT_EQ(x.second.second.size(), expected_map[x.first].second.size());
    for (int i = 0; i < x.second.second.size(); i++){
      EXPECT_EQ(x.second.second[i], expected_map[x.first].second[i]);
    }
    }

  }
}

TEST_P(UnitWalkerTests, PathTests3)
{
  //test ITE

  SolverConfiguration sc = GetParam();
  if (sc.is_logging_solver) {

    Term x = s->make_symbol("x", bvsort);
    Term y = s->make_symbol("y", bvsort);
    Term xe2 = s->make_term(Equal, x, s->make_term(2, bvsort));
    Term lhs = s->make_term(Ite, xe2, x, s->make_term(3, bvsort));
    Term fullform = s->make_term(Equal, lhs, y);

    UnorderedTermPairMap UndMap;
    TreeWalker iw(s, false, &UndMap);

    pair <Term, vector<int>> p1;
    p1 = iw.visit(fullform);

    UnorderedTermPairMap expected_map;
    //full formula: {}
    pair <Term, vector<int>> n0;
    n0.first = fullform;
    vector<int> n0path;
    n0.second = n0path;
    expected_map[fullform] = n0;
    //ite part: {0}
    pair <Term, vector<int>> n1;
    n1.first = fullform;
    vector<int> n1path = {0};
    n1.second = n1path;
    expected_map[lhs] = n1;
    //x=2: {0,0}
    pair <Term, vector<int>> n2;
    n2.first = fullform;
    vector<int> n2path = {0, 0};
    n2.second = n2path;
    expected_map[xe2] = n2;
    //x: {0,0,0}
    pair <Term, vector<int>> n3;
    n3.first = fullform;
    vector<int> n3path = {0, 0, 0};
    n3.second = n3path;
    expected_map[x] = n3;
    //2: {0,0,1}
    pair <Term, vector<int>> n4;
    n4.first = fullform;
    vector<int> n4path = {0, 0, 1};
    n4.second = n4path;
    expected_map[s->make_term(2, bvsort)] = n4;
    //3: {0,2}
    pair <Term, vector<int>> n5;
    n5.first = fullform;
    vector<int> n5path = {0, 2};
    n5.second = n5path;
    expected_map[s->make_term(3, bvsort)] = n5;
    //y: {1}
    pair <Term, vector<int>> n6;
    n6.first = fullform;
    vector<int> n6path = {1};
    n6.second = n6path;
    expected_map[y] = n6;

//    printMap(UndMap);

    //SEG FAULT SOMEWHERE IN THIS LOOP....
    for (auto const& x : UndMap){
      EXPECT_EQ(x.second.first, expected_map[x.first].first); //testing equivalence of first element in pair: the topmost node
      ASSERT_EQ(x.second.second.size(), expected_map[x.first].second.size());
      for (int i = 0; i < x.second.second.size(); i++){
        EXPECT_EQ(x.second.second[i], expected_map[x.first].second[i]);
      }
    }
  }
}

TEST_P(UnitWalkerTests, PathTests4UF)
{
  //test with Uninterpreted Functions
  SolverConfiguration sc = GetParam();
  if (sc.is_logging_solver) {

    Term x = s->make_symbol("x", bvsort);
    Term f = s->make_symbol("f", funsort);
    Term g = s->make_symbol("g", funsort);
    Term fx = s->make_term(Apply, f, x);
    Term gx = s->make_term(Apply, g, x);
    Term fullform = s->make_term(Equal, fx, gx);

    UnorderedTermPairMap UndMap;
    TreeWalker iw(s, false, &UndMap);

    pair <Term, vector<int>> p1;
    p1 = iw.visit(fullform);

    map<Term, pair<Term, vector<int>>> expected_map;
    pair <Term, vector<int>> n0;
    n0.first = fullform;
    vector<int> n0path;
    n0.second = n0path;
    expected_map[fullform] = n0;
    //f(x): {0}
    pair <Term, vector<int>> n1;
    n1.first = fullform;
    vector<int> n1path = {0};
    n1.second = n1path;
    expected_map[fx] = n1;
    //g(x): {1}
    pair <Term, vector<int>> n2;
    n2.first = fullform;
    vector<int> n2path = {1};
    n2.second = n2path;
    expected_map[gx] = n2;
    //f: {0,0}
    pair <Term, vector<int>> n3;
    n3.first = fullform;
    vector<int> n3path = {0, 0};
    n3.second = n3path;
    expected_map[f] = n3;
    //g: {1,0}
    pair <Term, vector<int>> n4;
    n4.first = fullform;
    vector<int> n4path = {1, 0};
    n4.second = n4path;
    expected_map[g] = n4;
    //x: {0,1}
    pair <Term, vector<int>> n5;
    n5.first = fullform;
    vector<int> n5path = {0, 1};
    n5.second = n5path;
    expected_map[x] = n5;

    //TODO do we want function names searched like this...

    //printMap(UndMap);

    for (auto const& x : UndMap){
      EXPECT_EQ(x.second.first, expected_map[x.first].first); //testing equivalence of first element in pair: the topmost node
      ASSERT_EQ(x.second.second.size(), expected_map[x.first].second.size());
      for (int i = 0; i < x.second.second.size(); i++){
        EXPECT_EQ(x.second.second[i], expected_map[x.first].second[i]);
      }
    }
  }
}
//TODO add test for UF with not just binary

TEST_P(UnitWalkerTests, FreshVars){
  //testing repeated values
  SolverConfiguration sc = GetParam();
  if (sc.is_logging_solver) {
  Term x = s->make_symbol("x", bvsort);
  Term y = s->make_symbol("y", bvsort);
  Term xpx = s->make_term(BVAdd, x, x);
  Term ypy = s->make_term(BVAdd, y, y);
  Term xp2 = s->make_term(BVAdd, x, s->make_term(2, bvsort));
  Term lmt = s->make_term(BVSub, xp2, xpx);
  Term rhs = s->make_term(BVAdd, ypy, lmt);
  Term fullform = s->make_term(Equal, xpx, rhs);

//  map<Term, pair<Term, vector<int>>> expected_map;
  //y: {1,0,0}
//  pair <Term, vector<int>> n5;
//  n5.first = fullform;
//  vector<int> n5path = {1, 0, 0};
//  n5.second = n5path;
//  expected_map[b0] = n5;
  //2: {1,1,0,1}
//  pair <Term, vector<int>> n7;
//  n7.first = fullform;
//  vector<int> n7path = {1, 1, 0, 1};
//  n7.second = n7path;
//  expected_map[b1] = n7;
  //x+2: {1,1,0}
//  pair <Term, vector<int>> n6;
//  n6.first = fullform;
//  vector<int> n6path = {1, 1, 0};
//  n6.second = n6path;
//  expected_map[b2] = n6;
  //x: {0,0}
//  pair <Term, vector<int>> n2;
//  n2.first = fullform;
//  vector<int> n2path = {0, 0};
//  n2.second = n2path;
//  expected_map[x] = n2;
  //y+y: {1,0}
//  pair <Term, vector<int>> n4;
//  n4.first = fullform;
//  vector<int> n4path = {1, 0};
//  n4.second = n4path;
//  expected_map[ypy] = n4;
  //(y+y)+(x+2)-(x+x): {1}
//  pair <Term, vector<int>> n3;
//  n3.first = fullform;
//  vector<int> n3path = {1};
//  n3.second = n3path;
//  expected_map[rhs] = n3;
  //x+x: {0}
//  pair <Term, vector<int>> n1;
//  n1.first = fullform;
//  vector<int> n1path = {0};
//  n1.second = n1path;
//  expected_map[xpx] = n1;
  //x+2-x+x: {1,1}
//  pair <Term, vector<int>> n8;
//  n8.first = fullform;
//  vector<int> n8path = {1, 1};
//  n8.second = n8path;
 // expected_map[lmt] = n8;
  //fullform: {}
//  pair <Term, vector<int>> n0;
//  n0.first = fullform;
//  vector<int> n0path;
//  n0.second = n0path;
//  expected_map[fullform] = n0;

  UnorderedTermPairMap UndMap;
  FreshTreeWalker ftw(s, false, &UndMap);

  pair <Term, vector<int>> p1;
  p1 = ftw.visit(fullform);
//  Term = p1.first;

  printMap(UndMap);

 // for (auto const& x : UndMap){
   // EXPECT_EQ(x.second.first, expected_map[x.first].first); //testing equivalence of first element in pair: the topmost node
    //ASSERT_EQ(x.second.second.size(), expected_map[x.first].second.size());
  //  for (int i = 0; i < x.second.second.size(); i++){
    //  EXPECT_EQ(x.second.second[i], expected_map[x.first].second[i]);
   // }
    //}
  }
}


INSTANTIATE_TEST_SUITE_P(ParametrizedUnitWalker,
                         UnitWalkerTests,
                         testing::ValuesIn(filter_solver_configurations({ TERMITER })));

}  // namespace smt_tests
