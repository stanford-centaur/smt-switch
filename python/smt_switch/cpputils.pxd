from .cppapi cimport c_Term, c_TermVec, c_UnorderedTermSet
from .cppenums cimport c_PrimOp


cdef extern from "utils.h" namespace "smt":
    void get_free_symbolic_consts(const c_Term & term, c_UnorderedTermSet & out) except +
    void get_free_symbols(const c_Term & term, c_UnorderedTermSet & out) except +
    void op_partition(c_PrimOp po, const c_Term & term, c_TermVec & out) except +
    void conjunctive_partition(const c_Term & term, c_TermVec & out, bint include_bvand) except +
