import pytest
import smt_switch as ss
from smt_switch.primops import Distinct, Equal, Select, Store


@pytest.mark.parametrize("create_solver", ss.solvers.values())
def test_array_read_over_write(create_solver):
    solver = create_solver()
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
