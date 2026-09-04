# SPDX-FileCopyrightText: 2020 the smt-switch authors
# SPDX-FileContributor: Makai Mann
# SPDX-License-Identifier: BSD-3-Clause

import pytest

import smt_switch as ss


@pytest.mark.parametrize("create_solver", ss.solvers.values())
def test_unsat_assumptions_simple(create_solver):
    solver = create_solver(logging=False)
    solver.set_opt("produce-unsat-assumptions", "true")

    boolsort = solver.make_sort(ss.sortkinds.BOOL)
    a = solver.make_symbol("a", boolsort)
    b = solver.make_symbol("b", boolsort)
    not_b = solver.make_term(ss.primops.Not, b)
    solver.check_sat_assuming([a, b, not_b])
    core = solver.get_unsat_assumptions()
    assert b in core, "expecting b to be in core"
    assert not_b in core, "expecting (not b) to be in core"
