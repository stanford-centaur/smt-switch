import pytest
import smt_switch as ss

solvers=[]
full_bv_support=[]
try:
    from smt_switch import create_btor_solver
    solvers.append(create_btor_solver)
    full_bv_support.append(create_btor_solver)
except:
    pass

try:
    from smt_switch import create_cvc4_solver
    solvers.append(create_cvc4_solver)
    # TODO: Add CVC4 back in once get_op / substitute is implemented
    # full_bv_support.append(create_cvc4_solver)
except:
    pass

try:
    from smt_switch import create_msat_solver
    solvers.append(create_msat_solver)
    full_bv_support.append(create_msat_solver)
except:
    pass


@pytest.mark.parametrize("create_solver", solvers)
def test_bvadd(create_solver):
    solver = create_solver()
    solver.set_opt('produce-models', 'true')
    solver.set_logic('QF_BV')

    bvsort8 = solver.make_sort(ss.sortkinds.BV, 8)
    x = solver.make_symbol('x', bvsort8)
    y = solver.make_symbol('y', bvsort8)
    xpy = solver.make_term(ss.primops.BVAdd, x, y)
    solver.assert_formula(solver.make_term(ss.primops.Equal, xpy, solver.make_term(6, bvsort8)))

    solver.check_sat()

    xv = solver.get_value(x)
    yv = solver.get_value(y)
    assert int(xv) + int(yv) == 6


@pytest.mark.parametrize("create_solver", solvers)
def test_hackers_delight(create_solver):
    # The following example has been adapted from the book
    # A Hacker's Delight by Henry S. Warren.
    #
    # Given variable x that can have either value a or value b. We want to
    # update x with a value other than the current one.
    #
    # the straightforward solution is:
    # if (x == a) x = b else x = a
    #
    # Two more efficient ways include:
    # 1. x = a xor b xor x
    # 2. x = a + b - x
    #
    # We want to check that these are correct

    solver = create_solver()
    solver.set_logic('QF_BV')
    solver.set_opt('produce-models', 'true')
    solver.set_opt('incremental', 'true')

    bv32 = solver.make_sort(ss.sortkinds.BV, 32)

    x = solver.make_symbol('x', bv32)
    a = solver.make_symbol('a', bv32)
    b = solver.make_symbol('b', bv32)

    # x is a or b
    x_eq_a = solver.make_term(ss.primops.Equal, x, a)
    solver.assert_formula(solver.make_term(ss.primops.And,
                                           x_eq_a,
                                           solver.make_term(ss.primops.Equal, x, b)))

    # Updated x value
    xn = solver.make_symbol('xn', bv32)
    # x after executing alternative code
    xn_ = solver.make_symbol('xn_', bv32)

    ite_assignment = solver.make_term(ss.primops.Equal,
                                      xn,
                                      solver.make_term(ss.primops.Ite,
                                                       x_eq_a,
                                                       b,
                                                       a))

    print("Asserting", ite_assignment)
    solver.assert_formula(ite_assignment)

    # Push a context -- all assertions and check-sat calls are in a different context
    solver.push()
    # Encoding option 1
    assignment1 = solver.make_term(ss.primops.Equal,
                                   xn_,
                                   solver.make_term(ss.primops.BVXor, a,
                                                    solver.make_term(ss.primops.BVXor, b, x)))

    solver.assert_formula(assignment1)
    solver.assert_formula(solver.make_term(ss.primops.Distinct, xn, xn_))
    r = solver.check_sat()
    assert(r.is_unsat())
    # Pop the context
    solver.pop()

    solver.push()
    assignment2 = solver.make_term(ss.primops.Equal,
                                   xn_,
                                   solver.make_term(ss.primops.BVSub,
                                                    solver.make_term(ss.primops.BVAdd, a, b),
                                                    x))
    solver.assert_formula(assignment2)
    solver.assert_formula(solver.make_term(ss.primops.Distinct, xn, xn_))
    r = solver.check_sat()
    assert(r.is_unsat())
    solver.pop()


@pytest.mark.parametrize("create_solver", full_bv_support)
def test_complex_expr(create_solver):
    from smt_switch import Op

    solver = create_solver()
    bv128 = solver.make_sort(ss.sortkinds.BV, 128)
    bv32 = solver.make_sort(ss.sortkinds.BV, 32)

    x = solver.make_symbol('x', bv128)
    y = solver.make_symbol('y', bv128)
    a = solver.make_symbol('a', bv32)
    b = solver.make_symbol('b', bv32)
    c = solver.make_symbol('c', bv32)
    d = solver.make_symbol('d', bv32)

    abcd = solver.make_term(ss.primops.Concat,
                            a,
                            solver.make_term(ss.primops.Concat,
                                             b,
                                             solver.make_term(ss.primops.Concat,
                                                              c, d)))

    t0 = solver.make_term(ss.primops.BVXor, x, y)
    t1 = solver.make_term(ss.primops.BVSub, x, abcd)
    t2 = solver.make_term(ss.primops.BVAdd, t0, t1)
    t3 = solver.make_term(Op(ss.primops.Extract, 31, 0), t0)
    t4 = solver.make_term(ss.primops.BVOr, t3, c)
    t5 = solver.make_term(ss.primops.BVAshr, b, d)
    t6 = solver.make_term(ss.primops.Concat,
                            t4,
                            solver.make_term(ss.primops.Concat,
                                            a,
                                            solver.make_term(ss.primops.Concat,
                                                            t5, b)))
    t7 = solver.make_term(ss.primops.Ite, solver.make_term(ss.primops.BVUle, x, y),
                            t2, t6)
    t8 = solver.make_term(ss.primops.BVLshr, t7, t0)

    t8_sub = solver.substitute(t8, {x:x, y:y, a:a, b:b, c:c, d:d})
    # should be identical
    assert t8 == t8_sub, "Expecting identical terms but got:\n\t%s\n\t%s"%(t8, t8_sub)
