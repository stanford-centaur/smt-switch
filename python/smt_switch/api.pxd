from .cppapi cimport (
    c_Op,
    c_Result,
    c_SmtInterpolator,
    c_SmtSolver,
    c_TermBuilder,
    c_Sort,
    c_SortingNetwork,
    c_Term,
)

cdef class Op:
    cdef c_Op op


cdef class Result:
    cdef c_Result cr


cdef class TermBuilder:
    cdef c_TermBuilder ctb


cdef class SmtSolver(TermBuilder):
    cdef c_SmtSolver css
    cdef void set_solver(self, c_SmtSolver css)


cdef class SmtInterpolator(TermBuilder):
    cdef c_SmtInterpolator csi
    cdef void set_interpolator(self, c_SmtInterpolator csi)


cdef class Sort:
    cdef c_Sort cs
    cdef TermBuilder solver


cdef class SortingNetwork:
    cdef c_SortingNetwork * csn
    cdef SmtSolver solver


cdef class Term:
    cdef c_Term ct
    cdef TermBuilder solver
