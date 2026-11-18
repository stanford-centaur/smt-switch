from .cppenums cimport c_InterpolatorKind, c_OpKind, c_SolverKind, c_SortKind

cdef class OpKind:
    cdef c_OpKind ck


cdef class SolverKind:
    cdef c_SolverKind ck


cdef class InterpolatorKind:
    cdef c_InterpolatorKind ck


cdef class SortKind:
    cdef c_SortKind sk
