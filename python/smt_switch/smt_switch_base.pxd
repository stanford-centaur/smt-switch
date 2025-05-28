from .smt_switch_core cimport c_Op, c_Result, c_SmtSolver, c_Sort, c_SortingNetwork, c_Term
from .smt_switch_enums cimport c_PrimOp, c_SolverAttribute, c_SolverEnum, c_SortKind

cdef class Op:
    cdef c_Op op


cdef class PrimOp:
    cdef c_PrimOp po


cdef class Result:
    cdef c_Result cr


cdef class SmtSolver:
    cdef c_SmtSolver css


cdef class SolverAttribute:
    cdef c_SolverAttribute sa


cdef class SolverEnum:
    cdef c_SolverEnum se


cdef class Sort:
    cdef c_Sort cs
    cdef SmtSolver _solver


cdef class SortKind:
    cdef c_SortKind sk


cdef class SortingNetwork:
    cdef c_SortingNetwork * csn
    cdef SmtSolver _solver


cdef class Term:
    cdef c_Term ct
    cdef SmtSolver _solver
