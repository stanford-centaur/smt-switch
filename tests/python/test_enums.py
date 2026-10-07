# SPDX-FileCopyrightText: 2021 the smt-switch authors
# SPDX-FileContributor: Makai Mann
# SPDX-License-Identifier: BSD-3-Clause

"""Test getters for enums (SortKind and PrimOp)."""

import pytest

import smt_switch as ss
from smt_switch import solverattr, solverenums

from .available_solvers import int_support_solvers


@pytest.mark.parametrize(
    "create_solver", [f for name, f in int_support_solvers.items()]
)
def test_sortkind(create_solver):
    solver = create_solver(logging=False)
    bvsort = solver.make_sort(ss.sortkinds.BV, 8)
    x = solver.make_symbol("x", bvsort)
    sk = x.get_sort().get_sort_kind()
    assert hash(ss.sortkinds.BV) == hash(sk)
    assert sk == ss.sortkinds.BV
    assert sk is ss.sortkinds.BV


@pytest.mark.parametrize(
    "create_solver", [f for name, f in int_support_solvers.items()]
)
def test_primop(create_solver):
    solver = create_solver(logging=False)
    bvsort = solver.make_sort(ss.sortkinds.BV, 8)
    x = solver.make_symbol("x", bvsort)
    y = solver.make_symbol("y", bvsort)
    xpy = solver.make_term(ss.primops.BVAdd, x, y)
    op = xpy.get_op()

    assert hash(ss.primops.BVAdd) == hash(op.prim_op)
    assert op.prim_op == ss.primops.BVAdd
    assert op.prim_op is ss.primops.BVAdd


@pytest.mark.parametrize(
    "name",
    [
        "BTOR",
        "BZLA",
        "BZLA_INTERPOLATOR",
        "CVC5",
        "CVC5_INTERPOLATOR",
        "GENERIC_SOLVER",
        "MSAT",
        "MSAT_INTERPOLATOR",
        "YICES2",
        "Z3",
    ],
)
def test_solver_enum(name):
    assert str(getattr(solverenums, name)) == name


@pytest.mark.parametrize(
    "name",
    [
        "ARRAY_FUN_BOOLS",
        "ARRAY_MODELS",
        "BOOL_BV1_ALIASING",
        "CONSTARR",
        "FULL_TRANSFER",
        "LOGGING",
        "PARAM_UNINTERP_SORT",
        "QUANTIFIERS",
        "TERMITER",
        "THEORY_BV",
        "THEORY_DATATYPE",
        "THEORY_INT",
        "THEORY_REAL",
        "THEORY_STR",
        "TIMELIMIT",
        "UNINTERP_SORT",
        "UNSAT_CORE",
    ],
)
def test_solver_attribute(name):
    assert str(getattr(solverattr, name)) == name
