# SPDX-FileCopyrightText: 2020 the smt-switch authors
# SPDX-FileContributor: Makai Mann
# SPDX-License-Identifier: BSD-3-Clause

import pytest

import smt_switch as ss

from . import available_solvers


@pytest.mark.parametrize(
    "create_solver", available_solvers.int_support_solvers.values()
)
def test_unit_bigint(create_solver):
    solver = create_solver(logging=False)
    intsort = solver.make_sort(ss.sortkinds.INT)

    bigint = solver.make_term(2**200, intsort)
    maxsint_64 = solver.make_term(int("0x7FFFFFFFFFFFFFFF", 16), intsort)

    solver.assert_formula(solver.make_term(ss.primops.Gt, bigint, maxsint_64))
    assert solver.check_sat().is_sat(), (
        "Expecting to represent a large integer without overflow"
    )


@pytest.mark.parametrize("create_solver", list(ss.solvers.values()))
@pytest.mark.parametrize("value", [0, 5, 2**64, 2**99 + 3])
def test_bv_value_to_int(create_solver, value):
    solver = create_solver(logging=False)
    solver.set_opt("produce-models", "true")
    bvsort = solver.make_sort(ss.sortkinds.BV, 100)

    x = solver.make_symbol("x", bvsort)
    solver.assert_formula(
        solver.make_term(ss.primops.Equal, x, solver.make_term(value, bvsort))
    )
    assert solver.check_sat().is_sat()
    assert int(solver.get_value(x)) == value


@pytest.mark.parametrize(
    "create_solver", list(available_solvers.int_support_solvers.values())
)
@pytest.mark.parametrize("value", [0, 5, -5, 2**70, -(2**70)])
def test_int_value_to_int(create_solver, value):
    solver = create_solver(logging=False)
    solver.set_opt("produce-models", "true")
    intsort = solver.make_sort(ss.sortkinds.INT)

    x = solver.make_symbol("x", intsort)
    solver.assert_formula(
        solver.make_term(ss.primops.Equal, x, solver.make_term(value, intsort))
    )
    assert solver.check_sat().is_sat()
    assert int(solver.get_value(x)) == value
