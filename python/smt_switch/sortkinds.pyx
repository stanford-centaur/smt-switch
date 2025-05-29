from .cppenums cimport (
    c_ARRAY,
    c_BOOL,
    c_BV,
    c_INT,
    c_REAL,
    c_FUNCTION,
)
from .enums cimport SortKind

cdef SortKind ARRAY = SortKind()
ARRAY.sk = c_ARRAY
globals()["ARRAY"] = ARRAY

cdef SortKind BOOL = SortKind()
BOOL.sk = c_BOOL
globals()["BOOL"] = BOOL

cdef SortKind BV = SortKind()
BV.sk = c_BV
globals()["BV"] = BV

cdef SortKind INT = SortKind()
INT.sk = c_INT
globals()["INT"] = INT

cdef SortKind REAL = SortKind()
REAL.sk = c_REAL
globals()["REAL"] = REAL

cdef SortKind FUNCTION = SortKind()
FUNCTION.sk = c_FUNCTION
globals()["FUNCTION"] = FUNCTION


attrs = dict(globals())
int2sortkind = dict()
for attr, pysk in attrs.items():
    if not attr.startswith("_"):
        int2sortkind[(<int> (<SortKind?> pysk).sk)] = pysk
