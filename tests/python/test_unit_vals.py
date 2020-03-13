import pytest
import smt_switch as ss
from smt_switch.primops import Distinct, Equal, Select, Store


@pytest.mark.parametrize("create_solver", [f for n, f in ss.solvers.items() if n != 'btor'])
def test_unit_bigint(create_solver):
    solver = create_solver()
    intsort = solver.make_sort(ss.sortkinds.INT)

    bigint = solver.make_term(2**200, intsort)
    maxsint_64 = solver.make_term(int("0x7FFFFFFFFFFFFFFF", 16), intsort)

    solver.assert_formula(solver.make_term(ss.primops.Gt, bigint, maxsint_64))
    assert solver.check_sat().is_sat(), "Expecting to represent a large integer without overflow"
