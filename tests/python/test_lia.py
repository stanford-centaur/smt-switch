###############################################################
# \file test_lia.py
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
import smt_switch as ss

@pytest.mark.parametrize("create_solver", [f for name, f in ss.solvers.items() if name != 'btor'])
def test_simple(create_solver):
    solver = create_solver(False)
    solver.set_opt('produce-models', 'true')
    solver.set_logic('QF_LIA')

    intsort = solver.make_sort(ss.sortkinds.INT)
    x = solver.make_symbol('x', intsort)
    y = solver.make_symbol('y', intsort)
    z = solver.make_symbol('z', intsort)

    two = solver.make_term(2, intsort)
    three = solver.make_term(3, intsort)
    five = solver.make_term(5, intsort)

    t1 = solver.make_term(ss.primops.Plus,
                          solver.make_term(ss.primops.Mult, two, x),
                          solver.make_term(ss.primops.Mult, three, y))
    t2 = solver.make_term(ss.primops.Minus,
                          solver.make_term(ss.primops.Mult, five, y),
                          solver.make_term(ss.primops.Mult, three, z))

    f1 = solver.make_term(ss.primops.Lt, t1, five)
    f2 = solver.make_term(ss.primops.Ge, t2, two)

    solver.assert_formula(f1)
    solver.assert_formula(f2)

    r = solver.check_sat()
    assert r.is_sat()

    xv = int(solver.get_value(x))
    yv = int(solver.get_value(y))
    zv = int(solver.get_value(z))

    assert 2*xv + 3*yv < 5
    assert 5*yv - 3*zv >= 2
