from .cppenums cimport (
    c_BTOR,
    c_BZLA,
    c_CVC5,
    c_GENERIC,
    c_MSAT,
    c_YICES2,
    c_Z3,
)
from .enums cimport SolverKind


cdef SolverKind BTOR = SolverKind()
BTOR.ck = c_BTOR
globals()["BTOR"] = BTOR

cdef SolverKind BZLA = SolverKind()
BZLA.ck = c_BZLA
globals()["BZLA"] = BZLA

cdef SolverKind CVC5 = SolverKind()
CVC5.ck = c_CVC5
globals()["CVC5"] = CVC5

cdef SolverKind GENERIC = SolverKind()
GENERIC.ck = c_GENERIC
globals()["GENERIC"] = GENERIC

cdef SolverKind MSAT = SolverKind()
MSAT.ck = c_MSAT
globals()["MSAT"] = MSAT

cdef SolverKind YICES2 = SolverKind()
YICES2.ck = c_YICES2
globals()["YICES2"] = YICES2

cdef SolverKind Z3 = SolverKind()
Z3.ck = c_Z3
globals()["Z3"] = Z3
