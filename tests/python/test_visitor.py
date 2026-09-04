# SPDX-FileCopyrightText: 2021 the smt-switch authors
# SPDX-FileContributor: Makai Mann
# SPDX-License-Identifier: BSD-3-Clause

"""Small test of identity visiting."""

import pytest

import smt_switch as ss
from smt_switch.primops import BVOr, BVUlt, Ite


@pytest.mark.parametrize(
    "create_solver", [f for name, f in ss.solvers.items() if name != "yices2"]
)
def test_identity_visit_basic(create_solver):
    solver = create_solver(logging=False)

    bv32 = solver.make_sort(ss.sortkinds.BV, 32)

    x = solver.make_symbol("x", bv32)
    y = solver.make_symbol("y", bv32)
    a = solver.make_symbol("a", bv32)
    b = solver.make_symbol("b", bv32)

    y_assignment = solver.make_term(
        Ite,
        solver.make_term(BVUlt, x, y),
        solver.make_term(BVOr, x, a),
        solver.make_term(BVOr, x, b),
    )

    idvisitor = ss.IdentityVisitor(solver)
    rebuilt_y_assignment = idvisitor.walk_dag(y_assignment)
    assert y_assignment == rebuilt_y_assignment
