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
