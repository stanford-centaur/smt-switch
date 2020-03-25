import pytest
import smt_switch as ss

@pytest.mark.parametrize("create_solver", ss.solvers.values())
def test_unit_op(create_solver):
    solver = create_solver()

    null_op = ss.Op()
    ext = ss.Op(ss.primops.Extract, 2, 0)

    x = solver.make_symbol('x', solver.make_sort(ss.sortkinds.BV, 4))

    assert not null_op, 'null op should return false for bool'
    assert ext, 'non-null op should return true for bool'
    try:
        null_op_x = solver.make_term(null_op, x)
        assert False, 'Should get a ValueError'
    except ValueError as e:
        pass
    except:
        assert False, 'Should have gotten a ValueError'

    ext_x = solver.make_term(ext, x)
    assert ext == ext_x.get_op(), 'Extraction ops should match'
    assert ext != null_op, 'Extract op should not be equivalent to a null op'


@pytest.mark.parametrize("create_solver", ss.solvers.values())
def test_sort(create_solver):
    solver = create_solver()

    boolsort = solver.make_sort(ss.sortkinds.BOOL)
    bvsort   = solver.make_sort(ss.sortkinds.BV, 8)
    arrsort  = solver.make_sort(ss.sortkinds.ARRAY, [bvsort, bvsort])

    # TODO: test functions when boolector supports querying the sort

    names = ['b', 'bv', 'a']
    sorts = [boolsort, bvsort, arrsort]

    for n, s in zip(names, sorts):
        t = solver.make_symbol(n, s)
        assert t.get_sort() == s
        assert t.get_sort().get_sort_kind() == s.get_sort_kind()


@pytest.mark.parametrize("create_solver", ss.solvers.values())
def test_unit_iter(create_solver):
    solver = create_solver()

    null_op = ss.Op()
    ext = ss.Op(ss.primops.Extract, 2, 0)

    bvsort = solver.make_sort(ss.sortkinds.BV, 4)
    x = solver.make_symbol('x', bvsort)
    f = solver.make_symbol('f', solver.make_sort(ss.sortkinds.FUNCTION, [bvsort, bvsort]))

    fx = solver.make_term(ss.primops.Apply, f, x)

    cnt = 0
    for t in fx:
        assert cnt != 0 or t == f, 'First child should be f'
        assert cnt != 1 or t == x, 'Second child should be x'
        cnt += 1

    assert cnt == 2, "Expecting two children"


@pytest.mark.parametrize("create_solver", ss.solvers.values())
def test_bool(create_solver):
    solver = create_solver()
    solver.set_opt("produce-models", "true")

    boolsort = solver.make_sort(ss.sortkinds.BOOL)
    x = solver.make_symbol("x", boolsort)
    y = solver.make_symbol('y', boolsort)

    solver.assert_formula(solver.make_term(ss.primops.And,
                                           x,
                                           solver.make_term(ss.primops.Not,
                                                            y)))
    solver.check_sat()
    xv = solver.get_value(x)
    yv = solver.get_value(y)

    assert bool(xv)
    print(yv)
    assert not bool(yv)

    try:
        val = bool(x)
        assert False, "Shouldn't be able to call bool on non-value"
    except:
        pass


@pytest.mark.parametrize("create_solver", ss.solvers.values())
def test_check_sat_assuming(create_solver):
    solver = create_solver()
    solver.set_opt("incremental", "true")
    boolsort = solver.make_sort(ss.sortkinds.BOOL)
    bvsort8  = solver.make_sort(ss.sortkinds.BV, 8)

    x = solver.make_symbol("x", bvsort8)
    b = solver.make_symbol("b", boolsort)

    xeq0 = solver.make_term(ss.primops.Equal, x, solver.make_term(0, bvsort8))
    solver.assert_formula(solver.make_term(ss.primops.Not, xeq0))
    solver.assert_formula(solver.make_term(ss.primops.Implies, b, xeq0))

    try:
        solver.check_sat_assuming([xeq0])
        assert False, "Expecting a thrown exception for check_sat_assuming with a formula"
    except:
        pass

    r = solver.check_sat_assuming([b])
    assert r.is_unsat()


@pytest.mark.parametrize("create_solver", ss.solvers.values())
def test_multi_arg_fun(create_solver):
    solver = create_solver()
    bvsort = solver.make_sort(ss.sortkinds.BV, 8)
    funsort = solver.make_sort(ss.sortkinds.FUNCTION, [bvsort]*8)

    vs=[]
    for i in range(7):
        vs.append(solver.make_symbol('x%i'%i, bvsort))

    vs2=[]
    for i in range(7):
        vs2.append(solver.make_symbol('y%i'%i, bvsort))

    f = solver.make_symbol('f', funsort)
    res = solver.make_term(ss.primops.Apply, [f] + vs)
    assert res == solver.make_term(ss.primops.Apply, f, *vs)

    res2 = solver.make_term(ss.primops.Apply, f, *vs2)
    assert res != res2
    args = [f] + vs2
    assert res2 == solver.make_term(ss.primops.Apply, args)
