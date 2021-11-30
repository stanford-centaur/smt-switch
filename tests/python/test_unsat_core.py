###############################################################
# \file test_unsat_core.py
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

@pytest.mark.parametrize("create_solver", ss.solvers.values())
def test_unsat_assumptions_simple(create_solver):
    solver = create_solver(False)
    solver.set_opt("produce-unsat-assumptions", "true")

    boolsort = solver.make_sort(ss.sortkinds.BOOL)
    a = solver.make_symbol("a", boolsort)
    b = solver.make_symbol("b", boolsort)
    notB = solver.make_term(ss.primops.Not, b)
    r = solver.check_sat_assuming([a, b, notB]);
    core = solver.get_unsat_assumptions()
    assert b in core, "expecting b to be in core"
    assert notB in core, "expecting (not b) to be in core"
