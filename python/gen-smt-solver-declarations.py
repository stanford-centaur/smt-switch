#!/usr/bin/env python


# This file generates the declarations and python implementation for creating solvers
# It needs to be auto-generated because they depend on which solvers it
# is being compiled with

import argparse

CREATE_BTOR='''
def create_btor_solver():
    cdef SmtSolver solver = SmtSolver()
    solver.css = cpp_create_btor_solver()
    return solver
solvers["btor"] = create_btor_solver
'''


CREATE_CVC4='''
def create_cvc4_solver():
    cdef SmtSolver solver = SmtSolver()
    solver.css = cpp_create_cvc4_solver()
    return solver
solvers["cvc4"] = create_cvc4_solver
'''


CREATE_MSAT='''
def create_msat_solver():
    cdef SmtSolver solver = SmtSolver()
    solver.css = cpp_create_msat_solver()
    return solver
solvers["msat"] = create_msat_solver
'''


DECLARE_BTOR='''
cdef extern from "boolector_factory.h":
    c_SmtSolver cpp_create_btor_solver "smt::BoolectorSolverFactory::create" () except +
'''


DECLARE_CVC4='''
cdef extern from "cvc4_factory.h":
    c_SmtSolver cpp_create_cvc4_solver "smt::CVC4SolverFactory::create" () except +
'''


DECLARE_MSAT='''
cdef extern from "msat_factory.h":
    c_SmtSolver cpp_create_msat_solver "smt::MsatSolverFactory::create" () except +
'''


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Generate smt_switch python binding implementations.")
    parser.add_argument('--dest-dir', help='Where to put the generated files', required=True)
    parser.add_argument('--btor', action='store_true', help='Build with Boolector')
    parser.add_argument('--cvc4', action='store_true', help='Build with CVC4')
    parser.add_argument('--msat', action='store_true', help='Build with MathSAT')

    args = parser.parse_args()
    dest_dir = args.dest_dir

    imports = []

    pxd = 'from smt_switch_imp cimport c_SmtSolver'
    pxi = '# collect available solvers here\nsolvers = {}\n\n%s'
    if args.btor:
        pxd += "\n" + DECLARE_BTOR
        pxi += "\n" + CREATE_BTOR
        imports.append('cpp_create_btor_solver')

    if args.cvc4:
        pxd += "\n" + DECLARE_CVC4
        pxi += "\n" + CREATE_CVC4
        imports.append('cpp_create_cvc4_solver')

    if args.msat:
        pxd += "\n" + DECLARE_MSAT
        pxi += "\n" + CREATE_MSAT
        imports.append('cpp_create_msat_solver')

    if imports:
        CREATE_IMPORTS ='from smt_solvers cimport ' + ','.join(imports)
    else:
        CREATE_IMPORTS = '# Built with no solvers...'

    with open(dest_dir + "/smt_solvers.pxd", 'w') as f:
        f.write(pxd)

    with open(dest_dir + "/smt_solvers.pxi", 'w') as f:
        f.write(pxi%CREATE_IMPORTS)
