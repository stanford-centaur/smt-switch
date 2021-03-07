###############################################################
# \file test_visitor.py
# \verbatim
# Top contributors (to current version):
#   Makai Mann
# This file is part of the smt-switch project.
# Copyright (c) 2020 by the authors listed in the file AUTHORS
# in the top-level source directory) and their institutional affiliations.
# All rights reserved.  See the file LICENSE in the top-level source
# directory for licensing information.\endverbatim
#
# \brief Small test of identity visiting
#

import pytest
import smt_switch as ss
from smt_switch.primops import Ite, Equal, BVOr, BVUlt

@pytest.mark.parametrize("create_solver", (f for f in ss.solvers.values()))
def test_identity_visit_basic(create_solver):
    solver = create_solver(False)

    bv32 = solver.make_sort(ss.sortkinds.BV, 32)

    x = solver.make_symbol('x', bv32)
    y = solver.make_symbol('y', bv32)
    a = solver.make_symbol('a', bv32)
    b = solver.make_symbol('b', bv32)

    y_assignment = solver.make_term(Ite,
                                    solver.make_term(BVUlt, x, y),
                                    solver.make_term(BVOr, x, a),
                                    solver.make_term(BVOr, x, b))

    idvisitor = ss.IdentityVisitor(solver)
    rebuilt_y_assignment = idvisitor.walk_dag(y_assignment)
    assert y_assignment == rebuilt_y_assignment
