from .cppenums cimport c_PrimOp, c_SolverEnum, c_SortKind

cdef class PrimOp:
    cdef c_PrimOp po


cdef class SolverEnum:
    cdef c_SolverEnum se


cdef class SortKind:
    cdef c_SortKind sk
