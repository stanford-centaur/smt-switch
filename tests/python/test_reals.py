import pytest
import smt_switch as ss
from smt_switch.sortkinds import REAL
from smt_switch.primops import Equal, Ge, Lt, Minus, Mult, Plus
import available_solvers

termiter_and_int_keys = available_solvers.termiter_support_solvers.keys() & available_solvers.int_support_solvers.keys()
termiter_and_int_solvers = [f for f in {ss.solvers[n] for n in termiter_and_int_keys}]

@pytest.mark.parametrize("create_solver", termiter_and_int_solvers)
def test_reals_simple(create_solver):
    solver = create_solver()
    solver.set_logic('QF_LRA')

    realsort = solver.make_sort(REAL)

    x = solver.make_symbol('x', realsort)
    y = solver.make_symbol('y', realsort)

    c1 = solver.make_term(2, realsort)
    c2 = solver.make_term('457/32', realsort)
    c3 = solver.make_term('1.352968', realsort)
    c4 = solver.make_term('457/64', realsort)
    print(c4)

    solver.assert_formula(solver.make_term(Ge, solver.make_term(Minus,
                                                                solver.make_term(Mult, c1, x),
                                                                solver.make_term(Mult, c2, y)), c1))
    solver.assert_formula(solver.make_term(Lt, solver.make_term(Minus, x, solver.make_term(1, realsort)),
                                           solver.make_term(Mult, c4, y)))
    r = solver.check_sat()
    assert r.is_unsat()


@pytest.mark.parametrize("create_solver", [f for n, f in ss.solvers.items() if n != 'btor'])
def test_reals_subs_check(create_solver):
    solver = create_solver()
    solver.set_logic('QF_LRA')
    solver.set_opt('produce-models', 'true')
    solver.set_opt('incremental', 'true')

    realsort = solver.make_sort(REAL)

    x = solver.make_symbol('x', realsort)
    y = solver.make_symbol('y', realsort)
    z = solver.make_symbol('z', realsort)

    three = solver.make_term(3, realsort)
    ten   = solver.make_term(10, realsort)
    c     = solver.make_term("1237/5", realsort)

    constraint1 = solver.make_term(Lt, solver.make_term(Plus,
                                                        solver.make_term(Mult, three, x),
                                                        solver.make_term(Mult, c, y)),
                                   ten)

    constraint2 = solver.make_term(Ge, solver.make_term(Minus,
                                                        y,
                                                        solver.make_term(Mult, c, z)),
                                   three)

    solver.push()

    solver.assert_formula(constraint1)
    solver.assert_formula(constraint2)
    r = solver.check_sat()
    assert r.is_sat()

    xv = solver.get_value(x)
    yv = solver.get_value(y)
    zv = solver.get_value(z)

    solver.pop()

    substitution_map = {x:xv, y:yv, z:zv}
    c1sub = solver.substitute(constraint1, substitution_map)
    c2sub = solver.substitute(constraint2, substitution_map)

    solver.assert_formula(c1sub)
    solver.assert_formula(c2sub)
    r = solver.check_sat()
    assert r.is_sat()
