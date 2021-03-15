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

class UnitWalkerTests : public ::testing::Test,
                        public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());

    bvsort = s->make_sort(BV, 4);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort });
    fun2sort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort, bvsort });
    arrsort = s->make_sort(ARRAY, bvsort, bvsort);
    boolsort = s->make_sort(BOOL);
  }
  SmtSolver s;
  Sort bvsort, funsort, fun2sort, arrsort, boolsort;
};

/* Custom Tree Walker that builds up a map assigning fresh boolean variables to each occurrence of each term in the formula it visits.
 * One example of implementing visit_term to customize the behavior of the walker. */
class IndicatorTreeWalker : public TreeWalker {
  //iterator with which to name fresh variables: b0, ..., bn
  int b_iter {};

  using TreeWalker::TreeWalker;

  TreeWalkerStepResult visit_term(smt::Term & formula, smt::Term & term, std::vector<int> & path) override{

    Sort boolsort = solver_->make_sort(BOOL);

    //for each node visited, create a fresh boolean variable, bn, to map to an occurrence of a term in the formula (the formula
    //in which it occurs and the path indicating the term's location in the formula
    string var_name = string("b") + to_string(b_iter);
    Term b = solver_->make_symbol(var_name, boolsort);
    b_iter++;

    //builds up cache to map from a fresh boolean variable to a pair giving the full formula in which it occurs and the path indicating its place in the formula
    Op op = term->get_op();
    //occurrence of the term represented by the formula in which it is found and the path indicating its placement in the formula
    pair <Term, vector<int>> occ;
    if (!op.is_null())
    {
      //visiting a node rather than a leaf
      //vector the the children of the term we are visiting
      TermVec term_children;
      //populate vector of term's children
      for (auto t : term)
      {
        term_children.push_back(t);
      }
      occ.first = formula;
      occ.second = path;
      //occ_key is the key for the cache, which is the term itself, which maps to it's occurrence in the formula, represented by the pair occ
      Term occ_key;
      occ_key = solver_->make_term(op, term_children);
      save_in_cache(b, occ);
    }
    else
    {
      //visiting a leaf
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
  EXPECT_EQ(xp1, xp11);

  //expected_map:
  //x+1: <x+1, []>
  //x: <x+1, [0]>
  //1: <x+1, [1]>
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
    //testing equivalence of topmost node (first element in pair)
    EXPECT_EQ(x.second.first, expected_map[x.first].first);
    ASSERT_EQ(x.second.second.size(), expected_map[x.first].second.size());
    //testing path equivalence
    for (int i = 0; i < x.second.second.size(); i++){
      EXPECT_EQ(x.second.second[i], expected_map[x.first].second[i]);
    }
    }
  }
}

TEST_P(UnitWalkerTests, PathDecomp)
{
  SolverConfiguration sc = GetParam();
  if (sc.is_logging_solver) {
  //building up y=(x+1)+y
  Term x = s->make_symbol("x", bvsort);
  Term y = s->make_symbol("y", bvsort);
  Term xp1 = s->make_term(BVAdd, x, s->make_term(1, bvsort));
  Term xp1py = s->make_term(BVAdd, xp1, y);
  Term yexp1py = s->make_term(Equal, y, xp1py);

  /* expected_map:
   * y=x+1+y: <y=x+1+y, []>
   * y: <y=x+1+y, [0]>
   * x+1+y: <y=x+1+y, [1]>
   * x+1: <y=x+1+y, [1,0]
   * x: <y=x+1+y, [1,0,0]>
   * 1: <y=x+1+y, [1,0,1]>
   */
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
  n5.first = yexp1py;
  vector<int> n5path = {1, 0, 1};
  n5.second = n5path;
  expected_map[s->make_term(1, bvsort)] = n5;

  UnorderedTermPairMap UndMap;
  TreeWalker iw(s, false, &UndMap);

  pair <Term, vector<int>> p1;
  p1 = iw.visit(yexp1py);

  for (auto const& x : UndMap){
    EXPECT_EQ(x.second.first, expected_map[x.first].first);
    ASSERT_EQ(x.second.second.size(), expected_map[x.first].second.size());
    //testing equivalence of second element in pair (path) by looping through vector of ints
    for (int i = 0; i < x.second.second.size(); i++){
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
  //building up (x+x)={(y+y)+[(x+2)-(x+x)]}
  Term x = s->make_symbol("x", bvsort);
  Term y = s->make_symbol("y", bvsort);
  Term xpx = s->make_term(BVAdd, x, x);
  Term ypy = s->make_term(BVAdd, y, y);
  Term xp2 = s->make_term(BVAdd, x, s->make_term(2, bvsort));
  Term lmt = s->make_term(BVSub, xp2, xpx);
  Term rhs = s->make_term(BVAdd, ypy, lmt);
  Term fullform = s->make_term(Equal, xpx, rhs);

  /* expected_map:
   * (x+x)={(y+y)+[(x+2)-(x+x)]}: <(x+x)={(y+y)+[(x+2)-(x+x)]}, []>
   * x+x: <(x+x)={(y+y)+[(x+2)-(x+x)]}, [0]>
   * x: <(x+x)={(y+y)+[(x+2)-(x+x)]}, [0,0]>
   * (y+y)+[(x+2)-(x+x)]: <(x+x)={(y+y)+[(x+2)-(x+x)]}, [1]>
   * y+y: <(x+x)={(y+y)+[(x+2)-(x+x)]}, [1,0]>
   * y: <(x+x)={(y+y)+[(x+2)-(x+x)]}, [1,0,0]>
   * x+2: <(x+x)={(y+y)+[(x+2)-(x+x)]}, [1,1,0]>
   * 2: <(x+x)={(y+y)+[(x+2)-(x+x)]}, [1,1,0,1]>
   * (x+2)-(x+x): <(x+x)={(y+y)+[(x+2)-(x+x)]}, [1,1]>
   */
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

  for (auto const& x : UndMap){
    EXPECT_EQ(x.second.first, expected_map[x.first].first);
    ASSERT_EQ(x.second.second.size(), expected_map[x.first].second.size());
    for (int i = 0; i < x.second.second.size(); i++){
      EXPECT_EQ(x.second.second[i], expected_map[x.first].second[i]);
    }
    }
  }
}

TEST_P(UnitWalkerTests, SimplePathTests1)
{
  SolverConfiguration sc = GetParam();
  if (sc.is_logging_solver) {

  Term x = s->make_symbol("x", bvsort);

  UnorderedTermPairMap UndMap;
  TreeWalker iw(s, false, &UndMap);

  pair <Term, vector<int>> p1;
  p1 = iw.visit(x);

  /* expected_map:
   * x: <x, []>
   */
  map<Term, pair<Term, vector<int>>> expected_map;
  pair <Term, vector<int>> n0;
  n0.first = x;
  vector<int> n0path;
  n0.second = n0path;
  expected_map[x] = n0;

  for (auto const& x : UndMap){
    EXPECT_EQ(x.second.first, expected_map[x.first].first);
    ASSERT_EQ(x.second.second.size(), expected_map[x.first].second.size());
    for (int i = 0; i < x.second.second.size(); i++){
      EXPECT_EQ(x.second.second[i], expected_map[x.first].second[i]);
    }
    }

  }
}

TEST_P(UnitWalkerTests, SimplePathTests2)
{
  SolverConfiguration sc = GetParam();
  if (sc.is_logging_solver) {

  Term bv2 = s->make_term(2, bvsort);

  UnorderedTermPairMap UndMap;
  TreeWalker iw(s, false, &UndMap);

  pair <Term, vector<int>> p1;
  p1 = iw.visit(bv2);

  /* expected_map:
   * 2: <2, []>
   */
  map<Term, pair<Term, vector<int>>> expected_map;
  pair <Term, vector<int>> n0;
  n0.first = bv2;
  vector<int> n0path;
  n0.second = n0path;
  expected_map[bv2] = n0;

  for (auto const& x : UndMap){
    EXPECT_EQ(x.second.first, expected_map[x.first].first);
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

    //build up (ite (x=2) x 3) = y
    Term x = s->make_symbol("x", bvsort);
    Term y = s->make_symbol("y", bvsort);
    Term xe2 = s->make_term(Equal, x, s->make_term(2, bvsort));
    Term lhs = s->make_term(Ite, xe2, x, s->make_term(3, bvsort));
    Term fullform = s->make_term(Equal, lhs, y);

    UnorderedTermPairMap UndMap;
    TreeWalker iw(s, false, &UndMap);

    pair <Term, vector<int>> p1;
    p1 = iw.visit(fullform);

    /* expected_map:
     * (ite (x=2) x 3) = y: <(ite (x=2) x 3) = y, []>
     * (ite (x=2) x 3): <(ite (x=2) x 3) = y, [0]>
     * x=2: <(ite (x=2) x 3) = y, [0,0]>
     * x: <(ite (x=2) x 3) = y, [0,0,0]>
     * 2: <(ite (x=2) x 3) = y, [0,0,1]>
     * 3: <(ite (x=2) x 3) = y, [0,2]>
     * y: <(ite (x=2) x 3) = y, [1]>
     */
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

    for (auto const& x : UndMap){
      EXPECT_EQ(x.second.first, expected_map[x.first].first);
      ASSERT_EQ(x.second.second.size(), expected_map[x.first].second.size());
      for (int i = 0; i < x.second.second.size(); i++){
        EXPECT_EQ(x.second.second[i], expected_map[x.first].second[i]);
      }
    }
  }
}

TEST_P(UnitWalkerTests, PathTestsUF1)
{
  //test with Uninterpreted Functions

  SolverConfiguration sc = GetParam();
  if (sc.is_logging_solver) {

    //build up f(x) = g(x)
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

    /* expected_map:
     * f(x)=g(x): <f(x)=g(x), []>
     * f(x): <f(x)=g(x), [0]>
     * g(x): <f(x)=g(x), [1]>
     * f: <f(x)=g(x), [0,0]>
     * g: <f(x)=g(x), [1,0]>
     * x: <f(x)=g(x), [0,1]>
     */
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

    for (auto const& x : UndMap){
      EXPECT_EQ(x.second.first, expected_map[x.first].first);
      ASSERT_EQ(x.second.second.size(), expected_map[x.first].second.size());
      for (int i = 0; i < x.second.second.size(); i++){
        EXPECT_EQ(x.second.second[i], expected_map[x.first].second[i]);
      }
    }
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
    cout << pair.first << ": " << "<" << val_pair.first << ", (" << vectorToString(val_pair.second) << ")> }" << endl;
  }
}

TEST_P(UnitWalkerTests, PathTestsUF2)
{
  //test with Uninterpreted Functions

  SolverConfiguration sc = GetParam();
  if (sc.is_logging_solver) {

    //build up f(y,z) = g(x)
    Term x = s->make_symbol("x", bvsort);
    Term y = s->make_symbol("y", bvsort);
    Term z = s->make_symbol("z", bvsort);
    Term f = s->make_symbol("f", fun2sort);
    Term g = s->make_symbol("g", funsort);
    Term fyz = s->make_term(Apply, f, y, z);
    Term gx = s->make_term(Apply, g, x);
    Term fullform = s->make_term(Equal, fyz, gx);

    UnorderedTermPairMap UndMap;
    TreeWalker iw(s, false, &UndMap);

    pair <Term, vector<int>> p1;
    p1 = iw.visit(fullform);

    /* expected_map:
     * f(y,z) = g(x): <f(y,z) = g(x), []>
     * f(y,z): <f(y,z) = g(x), [0]>
     * f: <f(y,z) = g(x), [0,0]>
     * y: <f(y,z) = g(x), [0,1]>
     * z: <f(y,z) = g(x), [0,2]>
     * g(x): <f(y,z) = g(x), [1]>
     * g: <f(y,z) = g(x), [1,0]>
     * x: <f(y,z) = g(x), [1,1]>
     */
    map<Term, pair<Term, vector<int>>> expected_map;
    //f(y,z) = g(x): <f(y,z) = g(x), []>
    pair <Term, vector<int>> n0;
    n0.first = fullform;
    vector<int> n0path;
    n0.second = n0path;
    expected_map[fullform] = n0;
    //f(y,z): <f(y,z) = g(x), [0]>
    pair <Term, vector<int>> n1;
    n1.first = fullform;
    vector<int> n1path = {0};
    n1.second = n1path;
    expected_map[fyz] = n1;
    //f: <f(y,z) = g(x), [0,0]>
    pair <Term, vector<int>> n2;
    n2.first = fullform;
    vector<int> n2path = {0, 0};
    n2.second = n2path;
    expected_map[f] = n2;
    //y: <f(y,z) = g(x), [0,1]>
    pair <Term, vector<int>> n3;
    n3.first = fullform;
    vector<int> n3path = {0, 1};
    n3.second = n3path;
    expected_map[y] = n3;
    //z: <f(y,z) = g(x), [0,2]>
    pair <Term, vector<int>> n4;
    n4.first = fullform;
    vector<int> n4path = {0, 2};
    n4.second = n4path;
    expected_map[z] = n4;
    //g(x): <f(y,z) = g(x), [1]>
    pair <Term, vector<int>> n5;
    n5.first = fullform;
    vector<int> n5path = {1};
    n5.second = n5path;
    expected_map[gx] = n5;
    //g: <f(y,z) = g(x), [1,0]>
    pair <Term, vector<int>> n6;
    n6.first = fullform;
    vector<int> n6path = {1, 0};
    n6.second = n6path;
    expected_map[g] = n6;
    //x: <f(y,z) = g(x), [1,1]>
    pair <Term, vector<int>> n7;
    n7.first = fullform;
    vector<int> n7path = {1, 1};
    n7.second = n7path;
    expected_map[x] = n7;

    printMap(UndMap);

    for (auto const& x : UndMap){
      EXPECT_EQ(x.second.first, expected_map[x.first].first);
      ASSERT_EQ(x.second.second.size(), expected_map[x.first].second.size());
      for (int i = 0; i < x.second.second.size(); i++){
        EXPECT_EQ(x.second.second[i], expected_map[x.first].second[i]);
      }
    }
  }
}

TEST_P(UnitWalkerTests, FreshVars){
  //testing repeated values with fresh variables

  SolverConfiguration sc = GetParam();
  if (sc.is_logging_solver) {
  //build up (x+x) = {(y+y) + [(x+2)-(x+x)]}
  Term x = s->make_symbol("x", bvsort);
  Term y = s->make_symbol("y", bvsort);
  Term xpx = s->make_term(BVAdd, x, x);
  Term ypy = s->make_term(BVAdd, y, y);
  Term xp2 = s->make_term(BVAdd, x, s->make_term(2, bvsort));
  Term lmt = s->make_term(BVSub, xp2, xpx);
  Term rhs = s->make_term(BVAdd, ypy, lmt);
  Term fullform = s->make_term(Equal, xpx, rhs);

  UnorderedTermPairMap UndMap;
  IndicatorTreeWalker itw(s, false, &UndMap);

  pair <Term, vector<int>> p1;
  p1 = itw.visit(fullform);

  /*expected_map:
   * b0: <(x+x)={(y+y)+[(x+2)-(x+x)]} , []>, where b0 corresponds to (x+x)={(y+y)+[(x+2)-(x+x)]}
   * b1: <(x+x)={(y+y)+[(x+2)-(x+x)]} , [1]>, where b1 corresponds to {(y+y)+[(x+2)-(x+x)]}
   * b2: <(x+x)={(y+y)+[(x+2)-(x+x)]} , [1,1]>, where b2 corresponds to [(x+2)-(x+x)]
   * b3: <(x+x)={(y+y)+[(x+2)-(x+x)]} , [1,1,1]>, where b3 corresponds to (x+x)
   * b4: <(x+x)={(y+y)+[(x+2)-(x+x)]} , [1,1,1,1]>, where b4 corresponds to x
   * b5: <(x+x)={(y+y)+[(x+2)-(x+x)]} , [1,1,1,0]>, where b5 corresponds to x
   * b6: <(x+x)={(y+y)+[(x+2)-(x+x)]} , [1,1,0]>, where b6 corresponds to (x+2)
   * b7: <(x+x)={(y+y)+[(x+2)-(x+x)]} , [1,1,0,1]>, where b7 corresponds to 2
   * b8: <(x+x)={(y+y)+[(x+2)-(x+x)]} , [1,1,0,0]>, where b8 corresponds to x
   * b9: <(x+x)={(y+y)+[(x+2)-(x+x)]} , [1,0]>, where b9 corresponds to (y+y)
   * b10: <(x+x)={(y+y)+[(x+2)-(x+x)]} , [1,0,1]>, where b10 corresponds to y
   * b11: <(x+x)={(y+y)+[(x+2)-(x+x)]} , [1,0,0]>, where b11 corresponds to y
   * b12: <(x+x)={(y+y)+[(x+2)-(x+x)]} , [0]>, where b12 corresponds to (x+x)
   * b13: <(x+x)={(y+y)+[(x+2)-(x+x)]} , [0,1]>, where b13 corresponds to x
   * b14: <(x+x)={(y+y)+[(x+2)-(x+x)]} , [0,0]>, where b14 corresponds to x
   */

  vector<int> expected_path;
  for (auto const& p : UndMap){
    string s = p.first->to_string();
    if (s == "b0") {
      EXPECT_EQ(p.second.first, fullform);
      EXPECT_EQ(p.second.second.size(), 0);
    }
    else if (s == "b1"){
      EXPECT_EQ(p.second.first, fullform);
      ASSERT_EQ(p.second.second.size(), 1);
      EXPECT_EQ(p.second.second[0], 1);
    }
    else if (s == "b2"){
      EXPECT_EQ(p.second.first, fullform);
      expected_path = {1, 1};
      ASSERT_EQ(p.second.second.size(), 2);
      for(int i = 0; i < p.second.second.size(); i++){
        EXPECT_EQ(p.second.second[i], expected_path[i]);
      }
    }
    else if (s == "b3"){
      EXPECT_EQ(p.second.first, fullform);
      expected_path = {1, 1, 1};
      ASSERT_EQ(p.second.second.size(), 3);
      for(int i = 0; i < p.second.second.size(); i++){
        EXPECT_EQ(p.second.second[i], expected_path[i]);
      }
    }
    else if (s == "b4"){
      EXPECT_EQ(p.second.first, fullform);
      expected_path = {1, 1, 1, 1};
      ASSERT_EQ(p.second.second.size(), 4);
      for(int i = 0; i < p.second.second.size(); i++){
        EXPECT_EQ(p.second.second[i], expected_path[i]);
      }
    }
    else if (s == "b5"){
      EXPECT_EQ(p.second.first, fullform);
      expected_path = {1, 1, 1, 0};
      ASSERT_EQ(p.second.second.size(), 4);
      for(int i = 0; i < p.second.second.size(); i++){
        EXPECT_EQ(p.second.second[i], expected_path[i]);
      }
    }
    else if (s == "b6"){
      EXPECT_EQ(p.second.first, fullform);
      expected_path = {1, 1, 0};
      ASSERT_EQ(p.second.second.size(), 3);
      for(int i = 0; i < p.second.second.size(); i++){
        EXPECT_EQ(p.second.second[i], expected_path[i]);
      }
    }
    else if (s == "b7"){
      EXPECT_EQ(p.second.first, fullform);
      expected_path = {1, 1, 0, 1};
      ASSERT_EQ(p.second.second.size(), 4);
      for(int i = 0; i < p.second.second.size(); i++){
        EXPECT_EQ(p.second.second[i], expected_path[i]);
      }
    }
    else if (s == "b8"){
      EXPECT_EQ(p.second.first, fullform);
      expected_path = {1, 1, 0, 0};
      ASSERT_EQ(p.second.second.size(), 4);
      for(int i = 0; i < p.second.second.size(); i++){
        EXPECT_EQ(p.second.second[i], expected_path[i]);
      }
    }
    else if (s == "b9"){
      EXPECT_EQ(p.second.first, fullform);
      expected_path = {1, 0};
      ASSERT_EQ(p.second.second.size(), 2);
      for(int i = 0; i < p.second.second.size(); i++){
        EXPECT_EQ(p.second.second[i], expected_path[i]);
      }
    }
    else if (s == "b10"){
      EXPECT_EQ(p.second.first, fullform);
      expected_path = {1, 0, 1};
      ASSERT_EQ(p.second.second.size(), 3);
      for(int i = 0; i < p.second.second.size(); i++){
        EXPECT_EQ(p.second.second[i], expected_path[i]);
      }
    }
    else if (s == "b11"){
      EXPECT_EQ(p.second.first, fullform);
      expected_path = {1, 0, 0};
      ASSERT_EQ(p.second.second.size(), 3);
      for(int i = 0; i < p.second.second.size(); i++){
        EXPECT_EQ(p.second.second[i], expected_path[i]);
      }
    }
    else if (s == "b12"){
      EXPECT_EQ(p.second.first, fullform);
      expected_path = {0};
      ASSERT_EQ(p.second.second.size(), 1);
      for(int i = 0; i < p.second.second.size(); i++){
        EXPECT_EQ(p.second.second[i], expected_path[i]);
      }
    }
    else if (s == "b13"){
      EXPECT_EQ(p.second.first, fullform);
      expected_path = {0, 1};
      ASSERT_EQ(p.second.second.size(), 2);
      for(int i = 0; i < p.second.second.size(); i++){
        EXPECT_EQ(p.second.second[i], expected_path[i]);
      }
    }
    else if (s == "b14"){
      EXPECT_EQ(p.second.first, fullform);
      expected_path = {0, 0};
      ASSERT_EQ(p.second.second.size(), 2);
      for(int i = 0; i < p.second.second.size(); i++){
        EXPECT_EQ(p.second.second[i], expected_path[i]);
      }
    }
    else {
      //no other keys should exist
      assert(false);
    }
  }
  }
}

INSTANTIATE_TEST_SUITE_P(ParametrizedUnitWalker,
                         UnitWalkerTests,
                         testing::ValuesIn(filter_solver_configurations({ TERMITER })));

}  // namespace smt_tests
