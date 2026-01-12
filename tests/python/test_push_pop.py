###############################################################
# \file test_push_pop.py
# \verbatim
# Top contributors (to current version):
#   Po-Chun Chien
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
import smt_switch as ss


@pytest.mark.parametrize("create_solver", ss.solvers.values())
def test_push_pop_levels(create_solver):
    solver = create_solver(False)
    solver.set_opt("incremental", "true")
    assert solver.get_context_level() == 0
    solver.push()
    assert solver.get_context_level() == 1
    solver.pop()
    assert solver.get_context_level() == 0
    solver.push(5)
    assert solver.get_context_level() == 5
    solver.pop(2)
    assert solver.get_context_level() == 3
    solver.pop_all()
    assert solver.get_context_level() == 0


@pytest.mark.parametrize("create_solver", ss.solvers.values())
def test_push_pop_solve(create_solver):
    solver = create_solver(False)
    solver.set_opt("incremental", "true")
    bool_sort = solver.make_sort(ss.sortkinds.BOOL)
    x = solver.make_symbol("x", bool_sort)
    y = solver.make_symbol("y", bool_sort)

    solver.push()
    solver.assert_formula(x)
    assert solver.check_sat().is_sat()

    solver.push()
    solver.assert_formula(solver.make_term(ss.primops.Not, y))
    assert solver.check_sat().is_sat()

    solver.push()
    solver.assert_formula(solver.make_term(ss.primops.Implies, x, y))
    assert solver.check_sat().is_unsat()

    solver.pop()
    assert solver.check_sat().is_sat()

    solver.pop()
    assert solver.check_sat().is_sat()
