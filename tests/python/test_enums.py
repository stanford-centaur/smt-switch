# SPDX-FileCopyrightText: 2021 the smt-switch authors
# SPDX-FileContributor: Makai Mann
# SPDX-License-Identifier: BSD-3-Clause

"""Test getters for enums (SortKind and OpKind)."""

import pytest

import smt_switch as ss
from smt_switch import solverenums

from .available_solvers import int_support_solvers


@pytest.mark.parametrize(
    "create_solver", [f for name, f in int_support_solvers.items()]
)
def test_sortkind(create_solver):
    solver = create_solver(logging=False)
    bvsort = solver.make_sort(ss.sortkinds.BV, 8)
    x = solver.make_symbol("x", bvsort)
    sk = x.get_sort().get_kind()
    assert hash(ss.sortkinds.BV) == hash(sk)
    assert sk == ss.sortkinds.BV
    assert sk is ss.sortkinds.BV


@pytest.mark.parametrize(
    ("name", "printed"),
    [
        ("ARRAY", "Array"),
        ("BOOL", "Bool"),
        ("BV", "BitVec"),
        ("INT", "Int"),
        ("REAL", "Real"),
        ("STRING", "String"),
        ("FUNCTION", "Function"),
        ("UNINTERPRETED", "Uninterpreted"),
        ("UNINTERPRETED_CONS", "UninterpretedSortConstructor"),
        ("DATATYPE", "Datatype"),
        ("CONSTRUCTOR", "Constructor"),
        ("SELECTOR", "Selector"),
        ("TESTER", "Tester"),
    ],
)
def test_sort_kind_name(name, printed):
    assert str(getattr(ss.sortkinds, name)) == printed


@pytest.mark.parametrize(
    "create_solver", [f for name, f in ss.solvers.items() if name != "btor"]
)
def test_uninterpreted_sort_kind(create_solver):
    solver = create_solver(logging=False)
    assert solver.make_sort("T", 0).get_kind() is ss.sortkinds.UNINTERPRETED
    assert solver.make_sort("F", 1).get_kind() is ss.sortkinds.UNINTERPRETED_CONS


@pytest.mark.parametrize(
    "create_solver", [f for name, f in int_support_solvers.items()]
)
def test_op_kind(create_solver):
    solver = create_solver(logging=False)
    bvsort = solver.make_sort(ss.sortkinds.BV, 8)
    x = solver.make_symbol("x", bvsort)
    y = solver.make_symbol("y", bvsort)
    xpy = solver.make_term(ss.opkinds.BVAdd, x, y)
    op = xpy.get_op()

    assert hash(ss.opkinds.BVAdd) == hash(op.kind)
    assert op.kind == ss.opkinds.BVAdd
    assert op.kind is ss.opkinds.BVAdd


# only cvc5 has strings
@pytest.mark.parametrize(
    "create_solver", [f for name, f in ss.solvers.items() if name == "cvc5"]
)
def test_string_op_kind(create_solver):
    solver = create_solver(logging=False)
    x = solver.make_symbol("x", solver.make_sort(ss.sortkinds.STRING))
    assert solver.make_term(ss.opkinds.StrLen, x).get_op().kind is ss.opkinds.StrLen


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
        "YICES2_INTERPOLATOR",
        "Z3",
    ],
)
def test_solver_enum(name):
    assert str(getattr(solverenums, name)) == name
