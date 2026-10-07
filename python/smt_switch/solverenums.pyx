from .cppenums cimport (
    c_BTOR,
    c_BZLA,
    c_CVC5,
    c_MSAT,
    c_YICES2,
    c_Z3,
    c_BZLA_INTERPOLATOR,
    c_MSAT_INTERPOLATOR,
    c_CVC5_INTERPOLATOR,
    c_GENERIC_SOLVER,
)
from .enums cimport SolverEnum


cdef SolverEnum BTOR = SolverEnum()
BTOR.se = c_BTOR
globals()["BTOR"] = BTOR

cdef SolverEnum BZLA = SolverEnum()
BZLA.se = c_BZLA
globals()["BZLA"] = BZLA

cdef SolverEnum CVC5 = SolverEnum()
CVC5.se = c_CVC5
globals()["CVC5"] = CVC5

cdef SolverEnum MSAT = SolverEnum()
MSAT.se = c_MSAT
globals()["MSAT"] = MSAT

cdef SolverEnum YICES2 = SolverEnum()
YICES2.se = c_YICES2
globals()["YICES2"] = YICES2

cdef SolverEnum Z3 = SolverEnum()
Z3.se = c_Z3
globals()["Z3"] = Z3

cdef SolverEnum BZLA_INTERPOLATOR = SolverEnum()
BZLA_INTERPOLATOR.se = c_BZLA_INTERPOLATOR
globals()["BZLA_INTERPOLATOR"] = BZLA_INTERPOLATOR

cdef SolverEnum MSAT_INTERPOLATOR = SolverEnum()
MSAT_INTERPOLATOR.se = c_MSAT_INTERPOLATOR
globals()["MSAT_INTERPOLATOR"] = MSAT_INTERPOLATOR

cdef SolverEnum CVC5_INTERPOLATOR = SolverEnum()
CVC5_INTERPOLATOR.se = c_CVC5_INTERPOLATOR
globals()["CVC5_INTERPOLATOR"] = CVC5_INTERPOLATOR

cdef SolverEnum GENERIC_SOLVER = SolverEnum()
GENERIC_SOLVER.se = c_GENERIC_SOLVER
globals()["GENERIC_SOLVER"] = GENERIC_SOLVER
