from libc.stdint cimport int32_t, int64_t, uint32_t, uint64_t
from libcpp.memory cimport shared_ptr
from libcpp.string cimport string
from libcpp.vector cimport vector

from enums cimport SortKind

ctypedef shared_ptr[AbsSort] Sort
ctypedef shared_ptr[AbsTerm] Term
ctypedef shared_ptr[AbsSmtSolver] SmtSolver


cdef extern from "<iostream>" namespace "std":
cdef cppclass ostream:
        pass
    ostream cout


cdef extern from "include/sort.h" namespace "smt":
   cdef cppclass AbsSort:
       AbsSort() except +
       string to_string() except +
       size_t hash() except +
       # Not declaring const methods -- not necessary for Cython?
       uint64_t get_width() except +
       Sort get_indexsort() except +
       Sort get_elemsort() except +
       vector[Sort] get_domain_sorts() except +
       Sort get_codomain_sort() except +
       bint compare(const Sort sort) except +
       SortKind get_sort_kind() except +


cdef extern from "include/ops.h" namespace "smt":
    cdef cppclass Op:
        Op() except +
        string to_string() except +


# TODO See if we can combine with above cdef extern
cdef extern from "include/ops.h" namespace "smt":
    bint operator==(Op op1, Op op2) except +
    bint operator!=(Op op1, Op op2) except +
    ostream& operator<<(ostream & output, const Op o) except +


cdef extern from "include/term.h" namespace "smt":
    cdef cppclass TermIter:
        TermIter() except +
        TermIter& operator++() except +
        Term operator*() except +
        bint operator==(const TermIter& other) except +
        bint operator!=(const TermIter& other) except +

    cdef cppclass AbsTerm:
        AbsTerm() except +
        size_t hash() except +
        bint compare(const Term& absterm) except +
        Op get_op() except +
        Sort get_sort() except +
        string to_string() except +
        bint is_symbolic_const() except +
        bint is_value() except +
        uint64_t to_int() except +
        TermIter begin() except +
        TermIter end() except +


# TODO See if we can combine with above cdef extern
cdef extern from "include/term.h" namespace "smt":
    bint operator==(const Term& t1, const Term& t2) except +
    bint operator!=(const Term& t1, const Term& t2) except +
    ostream& operator<<(ostream& output, const Term t) except +


cdef extern from "include/solver.h" namespace "smt":
    AbsSmtSolver() except +
    void set_opt(const string option, const string value) except +
    void set_logic(const string logic) except +
    void assert_formula(const Term & t) except +
    void Result check_sat() except +
