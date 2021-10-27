#!/usr/bin/env python


# This file generates the declarations and python implementation for creating solvers
# It needs to be auto-generated because they depend on which solvers it
# is being compiled with

import argparse

CREATE_BTOR='''
def create_btor_solver(logging):
    cdef SmtSolver solver = SmtSolver()
    solver.css = cpp_create_btor_solver(logging)
    return solver
solvers["btor"] = create_btor_solver
'''


CREATE_BITWUZLA='''
def create_bitwuzla_solver(logging):
    cdef SmtSolver solver = SmtSolver()
    solver.css = cpp_create_bitwuzla_solver(logging)
    return solver
solvers["bitwuzla"] = create_bitwuzla_solver
'''


CREATE_CVC5='''
def create_cvc5_solver(logging):
    cdef SmtSolver solver = SmtSolver()
    solver.css = cpp_create_cvc5_solver(logging)
    return solver
solvers["cvc5"] = create_cvc5_solver

def create_cvc5_interpolator():
    cdef SmtSolver solver = SmtSolver()
    solver.css = cpp_create_cvc5_interpolator()
    return solver
'''


CREATE_MSAT='''
def create_msat_solver(logging):
    cdef SmtSolver solver = SmtSolver()
    solver.css = cpp_create_msat_solver(logging)
    return solver
solvers["msat"] = create_msat_solver

def create_msat_interpolator():
    cdef SmtSolver solver = SmtSolver()
    solver.css = cpp_create_msat_interpolator()
    return solver
'''

CREATE_YICES2='''
def create_yices2_solver(logging):
    cdef SmtSolver solver = SmtSolver()
    solver.css = cpp_create_yices2_solver(logging)
    return solver
solvers["yices2"] = create_yices2_solver
'''


DECLARE_BTOR='''
cdef extern from "boolector_factory.h":
    c_SmtSolver cpp_create_btor_solver "smt::BoolectorSolverFactory::create" (bint logging) except +
'''


DECLARE_BITWUZLA='''
cdef extern from "bitwuzla_factory.h":
    c_SmtSolver cpp_create_bitwuzla_solver "smt::BitwuzlaSolverFactory::create" (bint logging) except +
'''


DECLARE_CVC5='''
cdef extern from "cvc5_factory.h":
    c_SmtSolver cpp_create_cvc5_solver "smt::Cvc5SolverFactory::create" (bint logging) except +
    c_SmtSolver cpp_create_cvc5_interpolator "smt::Cvc5SolverFactory::create_interpolating_solver" () except +
'''


DECLARE_MSAT='''
cdef extern from "msat_factory.h":
    c_SmtSolver cpp_create_msat_solver "smt::MsatSolverFactory::create" (bint logging) except +
    c_SmtSolver cpp_create_msat_interpolator "smt::MsatSolverFactory::create_interpolating_solver" () except +
'''

DECLARE_YICES2='''
cdef extern from "yices2_factory.h":
    c_SmtSolver cpp_create_yices2_solver "smt::Yices2SolverFactory::create" (bint logging) except +
'''


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Generate smt_switch python binding implementations.")
    parser.add_argument('--dest-dir', help='Where to put the generated files', required=True)
    parser.add_argument('--btor', action='store_true', help='Build with Boolector')
    parser.add_argument('--bitwuzla', action='store_true', help='Build with Bitwuzla')
    parser.add_argument('--cvc5', action='store_true', help='Build with CVC5')
    parser.add_argument('--msat', action='store_true', help='Build with MathSAT')
    parser.add_argument('--yices2', action='store_true', help='Build with Yices2')

    args = parser.parse_args()
    dest_dir = args.dest_dir

    imports = []

    pxd = 'from smt_switch cimport c_SmtSolver'
    pxi = '# collect available solvers here\nsolvers = {}\n\n%s'
    if args.btor:
        pxd += "\n" + DECLARE_BTOR
        pxi += "\n" + CREATE_BTOR
        imports.append('cpp_create_btor_solver')

    if args.bitwuzla:
        pxd += "\n" + DECLARE_BITWUZLA
        pxi += "\n" + CREATE_BITWUZLA
        imports.append('cpp_create_bitwuzla_solver')

    if args.cvc5:
        pxd += "\n" + DECLARE_CVC5
        pxi += "\n" + CREATE_CVC5
        imports.append('cpp_create_cvc5_solver')
        imports.append('cpp_create_cvc5_interpolator')

    if args.msat:
        pxd += "\n" + DECLARE_MSAT
        pxi += "\n" + CREATE_MSAT
        imports.append('cpp_create_msat_solver')
        imports.append('cpp_create_msat_interpolator')

    if args.yices2:
        pxd += "\n" + DECLARE_YICES2
        pxi += "\n" + CREATE_YICES2
        imports.append('cpp_create_yices2_solver')

    if imports:
        CREATE_IMPORTS ='from smt_solvers cimport ' + ','.join(imports)
    else:
        CREATE_IMPORTS = '# Built with no solvers...'

    with open(dest_dir + "/smt_solvers.pxd", 'w') as f:
        f.write(pxd)

    with open(dest_dir + "/smt_solvers.pxi", 'w') as f:
        f.write(pxi%CREATE_IMPORTS)
