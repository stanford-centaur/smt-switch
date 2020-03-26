import smt_switch as ss


termiter_support_solvers = {k:v for k, v in ss.solvers.items() if k != 'yices2'}
int_support_solvers      = {k:v for k, v in ss.solvers.items() if k != 'btor'}
