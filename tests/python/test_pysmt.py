# SPDX-FileCopyrightText: 2021 the smt-switch authors
# SPDX-FileContributor: Caleb Donovick
# SPDX-License-Identifier: BSD-3-Clause

import pytest

# pysmt is an optional dependency, so each module is bound through
# importorskip. Plain imports would have to sit below the skip, out of import
# order.
sl = pytest.importorskip("pysmt.logics")
sc = pytest.importorskip("pysmt.shortcuts")
st = pytest.importorskip("pysmt.typing")
fe = pytest.importorskip("smt_switch.pysmt_frontend")


@pytest.mark.parametrize("solver_str", fe.SWITCH_SOLVERS.keys())
@pytest.mark.parametrize(
    ("sort", "logic"),
    [
        (st.BV8, sl.QF_BV),
        (st.INT, sl.QF_LIA),
        (st.REAL, sl.QF_LRA),
    ],
)
@pytest.mark.parametrize("implicit", [True, False])
def test_basic(solver_str, sort, logic, implicit):
    x = sc.FreshSymbol(sort)
    # `<` builds a pysmt formula here rather than comparing at runtime, so the
    # bound is part of the problem statement, not a magic value.
    problem = sc.And(x < 2, x > 0)  # noqa: PLR2004
    x_val = None
    args = () if implicit else (logic,)

    if logic not in fe.SWITCH_SOLVERS[solver_str].LOGICS:
        with pytest.raises(RuntimeError), fe.Solver(solver_str, *args) as solver:
            solver.add_assertion(problem)
    else:
        with fe.Solver(solver_str, *args) as solver:
            solver.add_assertion(problem)
            assert solver.solve()
            if sort is not st.REAL:
                x_val = solver.get_py_value(x)
                assert x_val == 1
            else:
                x_val = solver.get_value(problem)
        assert x_val is not None
