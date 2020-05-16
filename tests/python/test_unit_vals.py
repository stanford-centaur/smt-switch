import pytest
import smt_switch as ss
from smt_switch.primops import Distinct, Equal, Select, Store
import available_solvers

termiter_and_int_keys = available_solvers.termiter_support_solvers.keys() & available_solvers.int_support_solvers.keys()
termiter_and_int_solvers = [f for f in {ss.solvers[n] for n in termiter_and_int_keys}]


@pytest.mark.parametrize("create_solver", termiter_and_int_solvers)
def test_unit_bigint(create_solver):
    solver = create_solver(False)
    intsort = solver.make_sort(ss.sortkinds.INT)

    bigint = solver.make_term(2**200, intsort)
    maxsint_64 = solver.make_term(int("0x7FFFFFFFFFFFFFFF", 16), intsort)

    solver.assert_formula(solver.make_term(ss.primops.Gt, bigint, maxsint_64))
    assert solver.check_sat().is_sat(), "Expecting to represent a large integer without overflow"
