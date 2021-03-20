#!/usr/bin/env python3
import smt_switch as ss
from smt_switch.primops import Apply, Distinct, Equal, Extract, BVAnd, BVUge

if __name__ == "__main__":
    s = ss.create_btor_solver(True)
    s.set_logic('QF_UFBV')
    s.set_opt('incremental', 'true')
    s.set_opt('produce-models', 'true')
    s.set_opt('produce-unsat-assumptions', 'true')
    bvs = s.make_sort(ss.sortkinds.BV, 32)
    funs = s.make_sort(ss.sortkinds.FUNCTION, [bvs, bvs])

    x = s.make_symbol('x', bvs)
    y = s.make_symbol('y', bvs)
    f = s.make_symbol('f', funs)

    ext = ss.Op(Extract, 15, 0)
    x0 = s.make_term(ext, x)
    y0 = s.make_term(ext, y)

    fx = s.make_term(Apply, f, x)
    fy = s.make_term(Apply, f, y)
    s.assert_formula(s.make_term(Distinct, fx, fy))

    s.push(1)
    s.assert_formula(s.make_term(Equal, x0, y0))
    print(s.check_sat())
    print(s.get_value(x))
    s.pop(1)

    xy = s.make_term(BVAnd, x, y)
    a1 = s.make_term(BVUge, xy, x);
    a2 = s.make_term(BVUge, xy, y);
    a3 = s.make_term(BVUge, x0, y0);
    print(s.check_sat_assuming([a1,a2,a3]))
    print(s.get_unsat_assumptions())
