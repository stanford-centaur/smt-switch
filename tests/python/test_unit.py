import pytest
import smt_switch as ss
import available_solvers

@pytest.mark.parametrize("create_solver", available_solvers.termiter_support_solvers.values())
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


@pytest.mark.parametrize("create_solver", available_solvers.termiter_support_solvers.values())
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
