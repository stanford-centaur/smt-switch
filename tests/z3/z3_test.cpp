#include <gtest/gtest.h>

#include "datatype.h"
#include "smt_defs.h"
#include "solver.h"
#include "sort.h"
#include "z3_factory.h"
#include "z3_sort.h"

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
