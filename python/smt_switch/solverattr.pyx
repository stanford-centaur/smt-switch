from .cppenums cimport (
    c_TERMITER,
    c_THEORY_INT,
    c_THEORY_REAL,
    c_ARRAY_MODELS,
    c_CONSTARR,
    c_FULL_TRANSFER,
    c_ARRAY_FUN_BOOLS,
    c_UNSAT_CORE,
    c_THEORY_DATATYPE,
    c_QUANTIFIERS,
    c_BOOL_BV1_ALIASING,
    c_TIMELIMIT,
)
from .enums cimport SolverAttribute


cdef SolverAttribute TERMITER = SolverAttribute()
TERMITER.sa = c_TERMITER
globals()["TERMITER"] = TERMITER

cdef SolverAttribute THEORY_INT = SolverAttribute()
THEORY_INT.sa = c_THEORY_INT
globals()["THEORY_INT"] = THEORY_INT

cdef SolverAttribute THEORY_REAL = SolverAttribute()
THEORY_REAL.sa = c_THEORY_REAL
globals()["THEORY_REAL"] = THEORY_REAL

cdef SolverAttribute ARRAY_MODELS = SolverAttribute()
ARRAY_MODELS.sa = c_ARRAY_MODELS
globals()["ARRAY_MODELS"] = ARRAY_MODELS

cdef SolverAttribute CONSTARR = SolverAttribute()
CONSTARR.sa = c_CONSTARR
globals()["CONSTARR"] = CONSTARR

cdef SolverAttribute FULL_TRANSFER = SolverAttribute()
FULL_TRANSFER.sa = c_FULL_TRANSFER
globals()["FULL_TRANSFER"] = FULL_TRANSFER

cdef SolverAttribute ARRAY_FUN_BOOLS = SolverAttribute()
ARRAY_FUN_BOOLS.sa = c_ARRAY_FUN_BOOLS
globals()["ARRAY_FUN_BOOLS"] = ARRAY_FUN_BOOLS

cdef SolverAttribute UNSAT_CORE = SolverAttribute()
UNSAT_CORE.sa = c_UNSAT_CORE
globals()["UNSAT_CORE"] = UNSAT_CORE

cdef SolverAttribute THEORY_DATATYPE = SolverAttribute()
THEORY_DATATYPE.sa = c_THEORY_DATATYPE
globals()["THEORY_DATATYPE"] = THEORY_DATATYPE

cdef SolverAttribute QUANTIFIERS = SolverAttribute()
QUANTIFIERS.sa = c_QUANTIFIERS
globals()["QUANTIFIERS"] = QUANTIFIERS

cdef SolverAttribute BOOL_BV1_ALIASING = SolverAttribute()
BOOL_BV1_ALIASING.sa = c_BOOL_BV1_ALIASING
globals()["BOOL_BV1_ALIASING"] = BOOL_BV1_ALIASING

cdef SolverAttribute TIMELIMIT = SolverAttribute()
TIMELIMIT.sa = c_TIMELIMIT
globals()["TIMELIMIT"] = TIMELIMIT
