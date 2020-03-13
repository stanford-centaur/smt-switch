import pytest
import smt_switch as ss
from typing import Set


def get_free_vars(t:ss.Term)->Set[ss.Term]:
    to_visit = [t]
    visited = set()

    free_vars = set()

    while to_visit:
        t = to_visit[-1]
        to_visit = to_visit[:-1]

        if t in visited:
            continue
        else:
            for tt in t:
                to_visit.append(tt)

            if t.is_symbolic_const():
                free_vars.add(t)

    return free_vars

# Note: Msat is only interpolant producing solver currently
@pytest.mark.parametrize("itp_name", [name for name in ss.solvers if name == 'msat'])
def test_simple_itp(itp_name):
    if itp_name == 'msat':
        itp = ss.create_msat_interpolator()
    else:
        raise NotImplementedError("Haven't handled interpolator {}".format(itp_name))

    intsort = itp.make_sort(ss.sortkinds.INT)
    x = itp.make_symbol('x', intsort)
    y = itp.make_symbol('y', intsort)
    z = itp.make_symbol('z', intsort)
    w = itp.make_symbol('w', intsort)

    # x < y
    A = itp.make_term(ss.primops.Lt,
                         x,
                         y)

    # y < w
    A = itp.make_term(ss.primops.And,
                         A,
                         itp.make_term(ss.primops.Lt,
                                           y,
                                           w))


    # z > w
    B = itp.make_term(ss.primops.Gt,
                         z,
                         w)

    # z < x
    B = itp.make_term(ss.primops.And,
                         B,
                         itp.make_term(ss.primops.Lt,
                                           z,
                                           x))

    I = itp.get_interpolant(A, B)
    assert I is not None

    free_vars = get_free_vars(I)
    assert y not in free_vars
    assert z not in free_vars
