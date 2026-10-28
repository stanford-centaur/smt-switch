/*!
 * \file z3-datatype.cpp
 * \brief Tests that a Z3 constructor decl can go into several datatypes.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Z3 overloads constructors across datatypes, so one constructor decl may
 * be added to several of them. Each must then give a self selector its own
 * datatype's sort. cvc5 and the generic solver refuse the reuse, as SMT-LIB
 * constructor names are global, so this is not a shared datatype test.
 */

#include <gtest/gtest.h>

#include <string>

#include "smt_defs.h"
#include "solver.h"
#include "sort.h"
#include "term.h"
#include "z3_factory.h"

using namespace smt;

namespace {

// the name of the sort that k's next selector returns in datatype dt
std::string next_sort(const SmtSolver & s, const Sort & dt)
{
  return s->get_selector(dt, "k", "next")
      ->get_sort()
      ->get_codomain_sort()
      ->to_string();
}

TEST(Z3Datatype, ReusedConstructorDeclGetsItsOwnSelfSort)
{
  SmtSolver s = Z3SolverFactory::create(false);
  DatatypeConstructorDecl k = s->make_datatype_constructor_decl("k");
  s->add_selector_self(k, "next");
  DatatypeDecl adecl = s->make_datatype_decl("A");
  DatatypeDecl bdecl = s->make_datatype_decl("B");
  s->add_constructor(adecl, s->make_datatype_constructor_decl("a0"));
  s->add_constructor(adecl, k);
  s->add_constructor(bdecl, s->make_datatype_constructor_decl("b0"));
  s->add_constructor(bdecl, k);
  Sort asort = s->make_sort(adecl);
  Sort bsort = s->make_sort(bdecl);

  EXPECT_EQ(next_sort(s, asort), "A");
  EXPECT_EQ(next_sort(s, bsort), "B");
}

TEST(Z3Datatype, ReusedInDatatypeSorts)
{
  SmtSolver s = Z3SolverFactory::create(false);
  DatatypeConstructorDecl k = s->make_datatype_constructor_decl("k");
  s->add_selector_self(k, "next");
  DatatypeDecl adecl = s->make_datatype_decl("A");
  DatatypeDecl bdecl = s->make_datatype_decl("B");
  s->add_constructor(adecl, s->make_datatype_constructor_decl("a0"));
  s->add_constructor(adecl, k);
  s->add_constructor(bdecl, s->make_datatype_constructor_decl("b0"));
  s->add_constructor(bdecl, k);
  Sort asort = s->make_datatype_sorts({ adecl }).at(0);
  Sort bsort = s->make_datatype_sorts({ bdecl }).at(0);

  EXPECT_EQ(next_sort(s, asort), "A");
  EXPECT_EQ(next_sort(s, bsort), "B");
}

}  // namespace
