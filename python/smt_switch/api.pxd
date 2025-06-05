from .cppapi cimport c_Op, c_Result, c_SmtSolver, c_Sort, c_SortingNetwork, c_Term

cdef class Op:
    cdef c_Op op


cdef class Result:
    cdef c_Result cr


cdef class SmtSolver:
    cdef c_SmtSolver css


cdef class Sort:
    cdef c_Sort cs
    cdef SmtSolver _solver


cdef class SortingNetwork:
    cdef c_SortingNetwork * csn
    cdef SmtSolver _solver


cdef class Term:
    cdef c_Term ct
    cdef SmtSolver _solver
