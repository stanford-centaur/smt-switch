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


# Only bitwuzla, cvc5 and msat expose an interpolator to Python; btor, yices2
# and z3 have no interpolation support at all. Every solver is parametrized so
# the report names the ones it skipped.
@pytest.mark.parametrize("theory", ["int", "bv"])
@pytest.mark.parametrize("itp_name", sorted(ss.solvers))
def test_simple_itp(itp_name, theory):
    try:
        create_interpolator = getattr(ss, f"create_{itp_name}_interpolator")
    except AttributeError:
        pytest.skip(f"{itp_name} exposes no interpolator to Python")
    if theory == "int" and itp_name == "bitwuzla":
        pytest.skip("bitwuzla has no integers")
    itp = create_interpolator()

    # the queries order the symbols, so unsigned bit-vector comparisons keep
    # them unsatisfiable
    if theory == "int":
        sort = itp.make_sort(ss.sortkinds.INT)
        lt, gt = ss.primops.Lt, ss.primops.Gt
    else:
        sort = itp.make_sort(ss.sortkinds.BV, 8)
        lt, gt = ss.primops.BVUlt, ss.primops.BVUgt
    x = itp.make_symbol("x", sort)
    y = itp.make_symbol("y", sort)
    z = itp.make_symbol("z", sort)
    w = itp.make_symbol("w", sort)

    # x < y
    a = itp.make_term(lt, x, y)

    # y < w
    a = itp.make_term(ss.primops.And, a, itp.make_term(lt, y, w))

    # z > w
    b = itp.make_term(gt, z, w)

    # z < x
    b = itp.make_term(ss.primops.And, b, itp.make_term(lt, z, x))

    interpolant = itp.get_interpolant(a, b)
    assert interpolant is not None

    free_vars = get_free_vars(interpolant)
    assert y not in free_vars
    assert z not in free_vars
