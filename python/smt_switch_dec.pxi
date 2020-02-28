from libc.stdint cimport int32_t, int64_t, uint32_t, uint64_t
from libcpp.memory cimport shared_ptr
from libcpp.string cimport string
from libcpp.unordered_map cimport unordered_map
from libcpp.vector cimport vector

from smt_switch cimport c_PrimOp, c_SortKind

ctypedef shared_ptr[AbsSort] c_Sort
ctypedef shared_ptr[AbsTerm] c_Term
ctypedef shared_ptr[AbsSmtSolver] c_SmtSolver
ctypedef vector[c_Sort] c_SortVec
ctypedef vector[c_Term] c_TermVec
ctypedef unordered_map[c_Term, c_Term] c_UnorderedTermMap


cdef extern from "<iostream>" namespace "std":
    cdef cppclass ostream:
        pass
    ostream cout


cdef extern from "sort.h" namespace "smt":
    cdef cppclass AbsSort:
        AbsSort() except +
        string to_string() except +
        size_t hash() except +
        uint64_t get_width() except +
        c_Sort get_indexsort() except +
        c_Sort get_elemsort() except +
        c_SortVec get_domain_sorts() except +
        c_Sort get_codomain_sort() except +
        bint compare(const c_Sort sort) except +
        c_SortKind get_sort_kind() except +


cdef extern from "ops.h" namespace "smt":
    cdef cppclass c_Op "smt::Op":
        c_Op() except +
        c_Op(c_PrimOp o) except +
        c_Op(c_PrimOp o, uint64_t idx0) except +
        c_Op(c_PrimOp o, uint64_t idx0, uint64_t idx1) except +
        string to_string() except +
        bint is_null() except +
        c_PrimOp prim_op
        uint64_t num_idx
        uint64_t idx0
        uint64_t idx1

    bint operator==(c_Op op1, c_Op op2) except +
    bint operator!=(c_Op op1, c_Op op2) except +
    ostream& operator<<(ostream & output, const c_Op o) except +


cdef extern from "term.h" namespace "smt":
    cdef cppclass c_TermIter "smt::TermIter":
        c_TermIter() except +
        c_TermIter& operator++() except +
        c_Term operator*() except +
        bint operator==(const c_TermIter& other) except +
        bint operator!=(const c_TermIter& other) except +

    cdef cppclass AbsTerm:
        AbsTerm() except +
        size_t hash() except +
        bint compare(const c_Term& absterm) except +
        c_Op get_op() except +
        c_Sort get_sort() except +
        string to_string() except +
        bint is_symbolic_const() except +
        bint is_value() except +
        uint64_t to_int() except +
        c_TermIter begin() except +
        c_TermIter end() except +

    bint operator==(const c_Term& t1, const c_Term& t2) except +
    bint operator!=(const c_Term& t1, const c_Term& t2) except +
    ostream& operator<<(ostream& output, const c_Term t) except +


cdef extern from "result.h" namespace "smt":
    cdef cppclass c_Result "smt::Result":
        bint is_sat() except +
        bint is_unsat() except +
        bint is_unknown() except +
        bint is_null() except +
        string to_string() except+


cdef extern from "solver.h" namespace "smt":
    cdef cppclass AbsSmtSolver:
        AbsSmtSolver() except +
        void set_opt(const string option, const string value) except +
        void set_logic(const string logic) except +
        void assert_formula(const c_Term & t) except +
        c_Result check_sat() except +
        c_Result check_sat_assuming(const c_TermVec & assumptions) except +
        void push(uint64_t num) except +
        void pop(uint64_t num) except +
        c_Term get_value(c_Term& t) except +
        c_Sort make_sort(const string name, uint64_t arity) except +
        c_Sort make_sort(const c_SortKind sk) except +
        c_Sort make_sort(const c_SortKind sk, uint64_t size) except +
        c_Sort make_sort(const c_SortKind sk, const c_Sort & sort1) except +
        c_Sort make_sort(const c_SortKind sk, const c_Sort & sort1, const c_Sort & sort2) except +
        c_Sort make_sort(const c_SortKind sk, const c_Sort & sort1, const c_Sort & sort2, const c_Sort & sort3) except +
        c_Sort make_sort(const c_SortKind sk, const c_SortVec & sorts) except +
        c_Term make_term(bint b) except +
        c_Term make_term(const string val, const c_Sort & sort) except +
        c_Term make_term(const string val, const c_Sort & sort, uint64_t base) except +
        c_Term make_term(const c_Term & val, const c_Sort & sort) except +
        c_Term make_symbol(const string name, const c_Sort & sort) except +
        c_Term make_term(const c_Op op, const c_Term & t) except +
        c_Term make_term(const c_Op op, const c_Term & t0, const c_Term & t1) except +
        c_Term make_term(const c_Op op, const c_Term & t0, const c_Term & t1, const c_Term & t2) except +
        c_Term make_term(const c_Op op, const c_TermVec & terms) except +
        void reset() except +
        void reset_assertions() except +
        c_Term substitute(const c_Term term, const c_UnorderedTermMap & substitution_map) except +
        bint get_interpolant(const c_Term & A, const c_Term & B, c_Term & out_I) except +


cdef class Op:
    cdef c_Op op

cdef class Result:
    cdef c_Result cr

cdef class Sort:
    cdef c_Sort cs
    cdef SmtSolver _solver

cdef class Term:
    cdef c_Term ct
    cdef SmtSolver _solver

cdef class SmtSolver:
    cdef c_SmtSolver css
