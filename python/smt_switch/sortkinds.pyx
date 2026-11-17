from .cppenums cimport (
    c_ARRAY,
    c_BOOL,
    c_BV,
    c_INT,
    c_REAL,
    c_STRING,
    c_FUNCTION,
    c_UNINTERPRETED,
    c_UNINTERPRETED_CONS,
    c_DATATYPE,
    c_CONSTRUCTOR,
    c_SELECTOR,
    c_TESTER,
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

cdef SortKind STRING = SortKind()
STRING.sk = c_STRING
globals()["STRING"] = STRING

cdef SortKind FUNCTION = SortKind()
FUNCTION.sk = c_FUNCTION
globals()["FUNCTION"] = FUNCTION

cdef SortKind UNINTERPRETED = SortKind()
UNINTERPRETED.sk = c_UNINTERPRETED
globals()["UNINTERPRETED"] = UNINTERPRETED

cdef SortKind UNINTERPRETED_CONS = SortKind()
UNINTERPRETED_CONS.sk = c_UNINTERPRETED_CONS
globals()["UNINTERPRETED_CONS"] = UNINTERPRETED_CONS

cdef SortKind DATATYPE = SortKind()
DATATYPE.sk = c_DATATYPE
globals()["DATATYPE"] = DATATYPE

cdef SortKind CONSTRUCTOR = SortKind()
CONSTRUCTOR.sk = c_CONSTRUCTOR
globals()["CONSTRUCTOR"] = CONSTRUCTOR

cdef SortKind SELECTOR = SortKind()
SELECTOR.sk = c_SELECTOR
globals()["SELECTOR"] = SELECTOR

cdef SortKind TESTER = SortKind()
TESTER.sk = c_TESTER
globals()["TESTER"] = TESTER


attrs = {attr: pysk for attr, pysk in globals().items() if not attr.startswith("_")}
int2sortkind = dict()
for pysk in attrs.values():
    int2sortkind[(<int> (<SortKind?> pysk).sk)] = pysk
