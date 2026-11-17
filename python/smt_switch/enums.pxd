from .cppenums cimport c_OpKind, c_SolverEnum, c_SortKind

cdef class OpKind:
    cdef c_OpKind ck


cdef class SolverEnum:
    cdef c_SolverEnum se


cdef class SortKind:
    cdef c_SortKind sk
