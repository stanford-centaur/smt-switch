# SPDX-FileCopyrightText: 2020 the smt-switch authors
# SPDX-FileContributor: Makai Mann
# SPDX-License-Identifier: BSD-3-Clause

import pytest

import smt_switch as ss


def get_free_vars(t: ss.Term) -> set[ss.Term]:
    to_visit = [t]
    visited = set()

    free_vars = set()

    while to_visit:
        t = to_visit[-1]
        to_visit = to_visit[:-1]

        if t in visited:
            continue
        for tt in t:
            to_visit.append(tt)

        if t.is_symbolic_const():
            free_vars.add(t)

    return free_vars


# Note: Msat is only interpolant producing solver currently
@pytest.mark.parametrize(
    "itp_name", [name for name in ss.solvers if name in {"msat", "cvc5"}]
)
def test_simple_itp(itp_name):
    try:
        create_interpolator = getattr(ss, f"create_{itp_name}_interpolator")
    except AttributeError as err:
        raise NotImplementedError(f"Haven't handled interpolator {itp_name}") from err
    itp = create_interpolator()

    intsort = itp.make_sort(ss.sortkinds.INT)
    x = itp.make_symbol("x", intsort)
    y = itp.make_symbol("y", intsort)
    z = itp.make_symbol("z", intsort)
    w = itp.make_symbol("w", intsort)

    # x < y
    a = itp.make_term(ss.primops.Lt, x, y)

    # y < w
    a = itp.make_term(ss.primops.And, a, itp.make_term(ss.primops.Lt, y, w))

    # z > w
    b = itp.make_term(ss.primops.Gt, z, w)

    # z < x
    b = itp.make_term(ss.primops.And, b, itp.make_term(ss.primops.Lt, z, x))

    interpolant = itp.get_interpolant(a, b)
    assert interpolant is not None

    free_vars = get_free_vars(interpolant)
    assert y not in free_vars
    assert z not in free_vars
