import pytest
import smt_switch as ss

# TODO: Add CVC4 back in once get_op / substitute is implemented
@pytest.mark.parametrize("create_solver", [cs for name, cs in ss.solvers.items() if name != 'cvc4'])
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
