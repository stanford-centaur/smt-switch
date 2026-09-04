###############################################################
# \file test_unit.py
# \verbatim
# Top contributors (to current version):
#   Makai Mann
# This file is part of the smt-switch project.
# Copyright (c) 2020 by the authors listed in the file AUTHORS
# in the top-level source directory) and their institutional affiliations.
# All rights reserved.  See the file LICENSE in the top-level source
# directory for licensing information.\endverbatim
#
# \brief
#
#
#

import pytest

import available_solvers
import smt_switch as ss


@pytest.mark.parametrize(
    "create_solver", available_solvers.termiter_support_solvers.values()
)
def test_unit_op(create_solver):
    solver = create_solver(False)

    null_op = ss.Op()
    ext = ss.Op(ss.primops.Extract, 2, 0)

    x = solver.make_symbol("x", solver.make_sort(ss.sortkinds.BV, 4))

    assert not null_op, "null op should return false for bool"
    assert ext, "non-null op should return true for bool"
    with pytest.raises(ValueError, match="Got a null Op in make_term"):
        solver.make_term(null_op, x)

    ext_x = solver.make_term(ext, x)
    assert ext == ext_x.get_op(), "Extraction ops should match"
    assert ext != null_op, "Extract op should not be equivalent to a null op"


@pytest.mark.parametrize("create_solver", ss.solvers.values())
def test_sort(create_solver):
    solver = create_solver(False)

    boolsort = solver.make_sort(ss.sortkinds.BOOL)
    bvsort = solver.make_sort(ss.sortkinds.BV, 8)
    arrsort = solver.make_sort(ss.sortkinds.ARRAY, [bvsort, bvsort])

    # TODO: test functions when boolector supports querying the sort

    names = ["b", "bv", "a"]
    sorts = [boolsort, bvsort, arrsort]

    for n, s in zip(names, sorts):
        t = solver.make_symbol(n, s)
        assert t.get_sort() == s
        assert t.get_sort().get_sort_kind() == s.get_sort_kind()


@pytest.mark.parametrize(
    "create_solver", available_solvers.termiter_support_solvers.values()
)
def test_unit_iter(create_solver):
    solver = create_solver(False)

    bvsort = solver.make_sort(ss.sortkinds.BV, 4)
    x = solver.make_symbol("x", bvsort)
    f = solver.make_symbol(
        "f", solver.make_sort(ss.sortkinds.FUNCTION, [bvsort, bvsort])
    )

    fx = solver.make_term(ss.primops.Apply, f, x)

    cnt = 0
    for t in fx:
        assert cnt != 0 or t == f, "First child should be f"
        assert cnt != 1 or t == x, "Second child should be x"
        cnt += 1

    assert cnt == 2, "Expecting two children"


@pytest.mark.parametrize("create_solver", ss.solvers.values())
def test_bool(create_solver):
    solver = create_solver(False)
    solver.set_opt("produce-models", "true")

    boolsort = solver.make_sort(ss.sortkinds.BOOL)
    x = solver.make_symbol("x", boolsort)
    y = solver.make_symbol("y", boolsort)

    solver.assert_formula(
        solver.make_term(ss.primops.And, x, solver.make_term(ss.primops.Not, y))
    )
    solver.check_sat()
    xv = solver.get_value(x)
    yv = solver.get_value(y)

    assert bool(xv)
    print(yv)
    assert not bool(yv)

    with pytest.raises(ValueError, match="Cannot call bool on"):
        bool(x)


@pytest.mark.parametrize("create_solver", ss.solvers.values())
def test_check_sat_assuming(create_solver):
    solver = create_solver(False)
    solver.set_opt("incremental", "true")
    boolsort = solver.make_sort(ss.sortkinds.BOOL)
    bvsort8 = solver.make_sort(ss.sortkinds.BV, 8)

    x = solver.make_symbol("x", bvsort8)
    b = solver.make_symbol("b", boolsort)

    xeq0 = solver.make_term(ss.primops.Equal, x, solver.make_term(0, bvsort8))
    solver.assert_formula(solver.make_term(ss.primops.Not, xeq0))
    solver.assert_formula(solver.make_term(ss.primops.Implies, b, xeq0))

    # Assumptions have to be literals. The backend rejects a formula by
    # throwing IncorrectUsageException, which Cython surfaces as RuntimeError.
    with pytest.raises(RuntimeError):
        solver.check_sat_assuming([xeq0])

    r = solver.check_sat_assuming([b])
    assert r.is_unsat()


@pytest.mark.parametrize("create_solver", ss.solvers.values())
def test_multi_arg_fun(create_solver):
    solver = create_solver(False)
    bvsort = solver.make_sort(ss.sortkinds.BV, 8)
    funsort = solver.make_sort(ss.sortkinds.FUNCTION, [bvsort] * 8)

    vs = [solver.make_symbol(f"x{i}", bvsort) for i in range(7)]
    vs2 = [solver.make_symbol(f"y{i}", bvsort) for i in range(7)]

    f = solver.make_symbol("f", funsort)
    res = solver.make_term(ss.primops.Apply, [f, *vs])
    assert res == solver.make_term(ss.primops.Apply, f, *vs)

    res2 = solver.make_term(ss.primops.Apply, f, *vs2)
    assert res != res2
    args = [f, *vs2]
    assert res2 == solver.make_term(ss.primops.Apply, args)
