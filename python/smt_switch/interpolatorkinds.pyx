from .cppenums cimport (
    c_BZLA_INTERPOLATOR,
    c_CVC5_INTERPOLATOR,
    c_MSAT_INTERPOLATOR,
    c_YICES2_INTERPOLATOR,
)
from .enums cimport InterpolatorKind


cdef InterpolatorKind BZLA = InterpolatorKind()
BZLA.ck = c_BZLA_INTERPOLATOR
globals()["BZLA"] = BZLA

cdef InterpolatorKind CVC5 = InterpolatorKind()
CVC5.ck = c_CVC5_INTERPOLATOR
globals()["CVC5"] = CVC5

cdef InterpolatorKind MSAT = InterpolatorKind()
MSAT.ck = c_MSAT_INTERPOLATOR
globals()["MSAT"] = MSAT

cdef InterpolatorKind YICES2 = InterpolatorKind()
YICES2.ck = c_YICES2_INTERPOLATOR
globals()["YICES2"] = YICES2
