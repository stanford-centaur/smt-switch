# SPDX-FileCopyrightText: 2021 the smt-switch authors
# SPDX-FileContributor: Makai Mann
# SPDX-License-Identifier: BSD-3-Clause

"""Test SortingNetwork through Python bindings.

See include/sorting_network.h for more information on the SortingNetwork class.
"""

from itertools import product

import pytest

import smt_switch as ss


@pytest.mark.parametrize(
    ("create_solver", "num_vars"), list(product(ss.solvers.values(), [3, 6, 8]))
)
def test_sorting_network(create_solver, num_vars):
    solver = create_solver(logging=False)
    solver.set_opt("produce-models", "true")
    solver.set_opt("incremental", "true")

    boolsort = solver.make_sort(ss.sortkinds.BOOL)
    boollist = [solver.make_symbol("b" + str(i), boolsort) for i in range(num_vars)]

    sn = ss.SortingNetwork(solver)
    sortedlist = sn.sorting_network(boollist)

    # Test each possible return value
    for num_true in range(num_vars + 1):
        solver.push()
        if num_true:
            # ensure there are at least num_true set to true
            solver.assert_formula(sortedlist[num_true - 1])
        if num_true < num_vars:
            # ensure there aren't more than num_true set to true
            solver.assert_formula(
                solver.make_term(ss.primops.Not, sortedlist[num_true])
            )
        res = solver.check_sat()
        assert res.is_sat()

        # The boolean here is the term's value, not a flag, so there is no
        # keyword form that would read better.
        true_ = solver.make_term(True)  # noqa: FBT003
        counted_true = 0
        for bb in boollist:
            val = solver.get_value(bb)
            if val == true_:
                counted_true += 1
        assert counted_true == num_true
        solver.pop()
