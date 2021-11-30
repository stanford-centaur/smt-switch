###############################################################
# \file test_enums.py
# \verbatim
# Top contributors (to current version):
#   Makai Mann
# This file is part of the smt-switch project.
# Copyright (c) 2020 by the authors listed in the file AUTHORS
# in the top-level source directory) and their institutional affiliations.
# All rights reserved.  See the file LICENSE in the top-level source
# directory for licensing information.\endverbatim
#
# \brief Test getters for enums (SortKind and PrimOp)
#
#

import pytest
import smt_switch as ss

from available_solvers import int_support_solvers


@pytest.mark.parametrize("create_solver", [f for name, f in int_support_solvers.items()])
def test_sortkind(create_solver):
    solver = create_solver(False)
    bvsort = solver.make_sort(ss.sortkinds.BV, 8)
    x = solver.make_symbol("x", bvsort)
    sk = x.get_sort().get_sort_kind()
    assert hash(ss.sortkinds.BV) == hash(sk)
    assert sk == ss.sortkinds.BV
    assert sk is ss.sortkinds.BV


@pytest.mark.parametrize("create_solver", [f for name, f in int_support_solvers.items()])
def test_primop(create_solver):
    solver = create_solver(False)
    bvsort = solver.make_sort(ss.sortkinds.BV, 8)
    x = solver.make_symbol("x", bvsort)
    y = solver.make_symbol("y", bvsort)
    xpy = solver.make_term(ss.primops.BVAdd, x, y)
    op = xpy.get_op()

    assert hash(ss.primops.BVAdd) == hash(op.prim_op)
    assert op.prim_op == ss.primops.BVAdd
    assert op.prim_op is ss.primops.BVAdd
