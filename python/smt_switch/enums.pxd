from .cppenums cimport c_PrimOp, c_SolverAttribute, c_SolverEnum, c_SortKind

cdef class PrimOp:
    cdef c_PrimOp po


cdef class SolverAttribute:
    cdef c_SolverAttribute sa


cdef class SolverEnum:
    cdef c_SolverEnum se


cdef class SortKind:
    cdef c_SortKind sk
