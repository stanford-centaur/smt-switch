from .cppenums cimport (
    c_BTOR,
    c_CVC5,
    c_MSAT,
    c_YICES2,
    c_MSAT_INTERPOLATOR,
    c_CVC5_INTERPOLATOR,
    c_GENERIC_SOLVER,
)
from .enums cimport SolverEnum


cdef SolverEnum BTOR = SolverEnum()
BTOR.se = c_BTOR
globals()["BTOR"] = BTOR

cdef SolverEnum CVC5 = SolverEnum()
CVC5.se = c_CVC5
globals()["CVC5"] = CVC5

cdef SolverEnum MSAT = SolverEnum()
MSAT.se = c_MSAT
globals()["MSAT"] = MSAT

cdef SolverEnum YICES2 = SolverEnum()
YICES2.se = c_YICES2
globals()["YICES2"] = YICES2

cdef SolverEnum MSAT_INTERPOLATOR = SolverEnum()
MSAT_INTERPOLATOR.se = c_MSAT_INTERPOLATOR
globals()["MSAT_INTERPOLATOR"] = MSAT_INTERPOLATOR

cdef SolverEnum CVC5_INTERPOLATOR = SolverEnum()
CVC5_INTERPOLATOR.se = c_CVC5_INTERPOLATOR
globals()["CVC5_INTERPOLATOR"] = CVC5_INTERPOLATOR

cdef SolverEnum GENERIC_SOLVER = SolverEnum()
GENERIC_SOLVER.se = c_GENERIC_SOLVER
globals()["GENERIC_SOLVER"] = GENERIC_SOLVER
