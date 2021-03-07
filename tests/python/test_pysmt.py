import pytest
import smt_switch as ss

pysmt = pytest.importorskip("pysmt")
from pysmt import shortcuts as sc
from pysmt import typing as st
from pysmt import logics as sl
import smt_switch.pysmt_frontend as fe

@pytest.mark.parametrize('solver_str', fe.SWITCH_SOLVERS.keys())
@pytest.mark.parametrize(('T', 'logic'), [
    (st.BV8, sl.QF_BV),
    (st.INT, sl.QF_LIA),
    (st.REAL, sl.QF_LRA),
    ])
@pytest.mark.parametrize('implicit', [True, False])
def test_basic(solver_str, T, logic, implicit):
    x = sc.FreshSymbol(T)
    problem = sc.And(x < 2, x > 0)
    x_val = None
    if implicit:
        args = ()
    else:
        args = (logic,)


    if logic not in fe.SWITCH_SOLVERS[solver_str].LOGICS:
        with pytest.raises(RuntimeError):
            with fe.Solver(solver_str, *args) as solver:
                solver.add_assertion(problem)
    else:
        with fe.Solver(solver_str, *args) as solver:
            solver.add_assertion(problem)
            assert solver.solve()
            if T is not st.REAL:
                x_val = solver.get_py_value(x)
                assert x_val == 1
            else:
                x_val = solver.get_value(problem)
        assert x_val is not None
