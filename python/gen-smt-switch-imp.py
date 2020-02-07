#!/usr/bin/env python


# This file generates the Python implementation for the Cython bindings
# It needs to be auto-generated because the solver creation functions
# Depend on which solvers it is being compiled with

import argparse

CREATE_BTOR='''
def create_btor_solver():
    cdef SmtSolver solver = SmtSolver()
    solver.css = cpp_create_btor_solver()
    return solver
'''


CREATE_CVC4='''
def create_cvc4_solver():
    cdef SmtSolver solver = SmtSolver()
    solver.css = cpp_create_cvc4_solver()
    return solver
'''


CREATE_MSAT='''
def create_msat_solver():
    cdef SmtSolver solver = SmtSolver()
    solver.css = cpp_create_msat_solver()
    return solver
'''


DECLARE_BTOR='''
cdef extern from "boolector_factory.h":
    SmtSolver cpp_create_btor_solver "smt::BoolectorSolverFactory::create" () except +
'''


DECLARE_CVC4='''
cdef extern from "cvc4_factory.h":
    SmtSolver cpp_create_cvc4_solver "smt::CVC4SolverFactory::create" () except +
'''


DECLARE_MSAT='''
cdef extern from "msat_factory.h":
    SmtSolver cpp_create_msat_solver "smt::MsatSolverFactory::create" () except +
'''


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Generate smt_switch python binding implementations.")
    parser.add_argument('--template-dir', help='The directory where the templates are kept', required=True)
    parser.add_argument('--dest-dir', help='Where to put the generated files', required=True)
    parser.add_argument('--btor', action='store_true', help='Build with Boolector')
    parser.add_argument('--cvc4', action='store_true', help='Build with CVC4')
    parser.add_argument('--msat', action='store_true', help='Build with MathSAT')

    args = parser.parse_args()
    template_dir = args.template_dir
    dest_dir = args.dest_dir

    pxd = None
    pxi = None
    imports = []
    with open(template_dir + '/smt_switch_imp_pxd.template', 'r') as f:
        pxd = f.read()
    assert pxd is not None, 'Error reading template pxd file'

    with open(template_dir + '/smt_switch_imp_pxi.template', 'r') as f:
        pxi = f.read()
    assert pxi is not None, 'Error reading template pxi file'

    if args.btor:
        pxd += "\n\n" + DECLARE_BTOR
        pxi += "\n\n" + CREATE_BTOR
        imports.append('cpp_create_btor_solver')

    if args.cvc4:
        pxd += "\n\n" + DECLARE_CVC4
        pxi += "\n\n" + CREATE_CVC4
        imports.append('cpp_create_cvc4_solver')

    if args.msat:
        pxd += "\n\n" + DECLARE_MSAT
        pxi += "\n\n" + CREATE_MSAT
        imports.append('cpp_create_msat_solver')

    if imports:
        CREATE_IMPORTS = 'from smt_switch_imp cimport ' + ','.join(imports)
    else:
        CREATE_IMPORTS = '# No solvers substituted'

    with open(dest_dir + "/smt_switch_imp.pxd", 'w') as f:
        f.write(pxd)

    with open(dest_dir + "/smt_switch_imp.pxi", 'w') as f:
        f.write(pxi%CREATE_IMPORTS)
