###############################################################
# \file test_sorting_network.py
# \verbatim
# Top contributors (to current version):
#   Makai Mann
# This file is part of the smt-switch project.
# Copyright (c) 2020 by the authors listed in the file AUTHORS
# in the top-level source directory) and their institutional affiliations.
# All rights reserved.  See the file LICENSE in the top-level source
# directory for licensing information.\endverbatim
#
# \brief Test SortingNetwork through Python bindings
#        see include/sorting_network.h for more information on the
#        SortingNetwork class
#

from itertools import product
import pytest

import smt_switch as ss

@pytest.mark.parametrize("create_solver,num_vars",
                         product(ss.solvers.values(), [3, 6, 8]))
def test_sorting_network(create_solver, num_vars):
    solver = create_solver(False)
    solver.set_opt('produce-models', 'true')
    solver.set_opt('incremental', 'true')

    boolsort = solver.make_sort(ss.sortkinds.BOOL)
    boollist = []
    for i in range(num_vars):
        boollist.append(solver.make_symbol('b' + str(i), boolsort))

    sn = ss.SortingNetwork(solver)
    sortedlist = sn.sorting_network(boollist)

    # Test each possible return value
    for num_true in range(num_vars+1):
        solver.push()
        if num_true:
            # ensure there are at least num_true set to true
            solver.assert_formula(sortedlist[num_true-1])
        if num_true < num_vars:
            # ensure there aren't more than num_true set to true
            solver.assert_formula(solver.make_term(ss.primops.Not, sortedlist[num_true]))
        res = solver.check_sat()
        assert res.is_sat()

        true_ = solver.make_term(True)
        counted_true = 0
        for bb in boollist:
            val = solver.get_value(bb)
            if val == true_:
                counted_true += 1
        assert counted_true == num_true
        solver.pop()
