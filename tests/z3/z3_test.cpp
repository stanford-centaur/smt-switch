/*!
 * \file z3_test.cpp
 * \brief Tests that a Z3 datatype sort wraps a Z3 datatype
 * \author Lindsey Stuntz
 * \date 2021
 * \copyright See the LICENSE file in the top-level source directory.
 */
#include <gtest/gtest.h>
#include <z3++.h>

#include <memory>
#include <string>

#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/sort.h"
#include "smt-switch/z3_factory.h"
#include "smt-switch/z3_sort.h"

using namespace smt;

TEST(Z3Test, DatatypeSortIsZ3Datatype)
{
  SmtSolver s = Z3SolverFactory::create(false);

  DatatypeDecl listSpec = s->make_datatype_decl("list");
  DatatypeConstructorDecl nildecl = s->make_datatype_constructor_decl("nil");
  DatatypeConstructorDecl consdecl = s->make_datatype_constructor_decl("cons");
  s->add_selector(consdecl, "head", s->make_sort(INT));
  s->add_selector_self(consdecl, "tail");
  s->add_constructor(listSpec, nildecl);
  s->add_constructor(listSpec, consdecl);
  Sort listsort = s->make_sort(listSpec);
  EXPECT_TRUE(
      std::static_pointer_cast<Z3Sort>(listsort)->get_z3_type().is_datatype());
}
