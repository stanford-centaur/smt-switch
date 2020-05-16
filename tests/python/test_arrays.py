###############################################################
# \file test_arrays.py
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
from smt_switch.primops import Distinct, Equal, Select, Store


@pytest.mark.parametrize("create_solver", ss.solvers.values())
def test_array_read_over_write(create_solver):
    solver = create_solver(False)
    solver.set_logic('QF_ABV')

    bvsort8  = solver.make_sort(ss.sortkinds.BV, 8)
    bvsort32 = solver.make_sort(ss.sortkinds.BV, 32)
    arrsort  = solver.make_sort(ss.sortkinds.ARRAY, bvsort8, bvsort32)

    i = solver.make_symbol('i', bvsort8)
    j = solver.make_symbol('j', bvsort8)
    e = solver.make_symbol('e', bvsort32)
    a = solver.make_symbol('a', arrsort)

    solver.assert_formula(solver.make_term(Distinct,
                                           solver.make_term(Select,
                                                            solver.make_term(Store, a, j, e),
                                                            i),
                                           e))
    solver.assert_formula(solver.make_term(Equal, i, j))
    r = solver.check_sat()
    assert r.is_unsat()


@pytest.mark.parametrize("create_solver", [f for n, f in ss.solvers.items() if n != 'btor'])
def test_array_lia_extensionality(create_solver):
    solver = create_solver(False)
    solver.set_logic('QF_ALIA')

    intsort = solver.make_sort(ss.sortkinds.INT)
    arrsort = solver.make_sort(ss.sortkinds.ARRAY, [intsort, intsort])

    i = solver.make_symbol('i', intsort)
    j = solver.make_symbol('j', intsort)
    a = solver.make_symbol('a', arrsort)
    b = solver.make_symbol('b', arrsort)

    solver.assert_formula(solver.make_term(Equal, a, b))
    solver.assert_formula(solver.make_term(Equal, i, j))
    solver.assert_formula(solver.make_term(Distinct,
                                           solver.make_term(Select, a, i),
                                           solver.make_term(Select, b, j)))
    r = solver.check_sat()
    assert r.is_unsat()
