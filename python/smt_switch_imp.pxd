from libc.stdint cimport int32_t, int64_t, uint32_t, uint64_t
from libcpp.memory cimport shared_ptr
from libcpp.string cimport string
from libcpp.unordered_map cimport unordered_map
from libcpp.vector cimport vector

from enums cimport SortKind
from enums cimport PrimOp

ctypedef shared_ptr[AbsSort] Sort
ctypedef shared_ptr[AbsTerm] Term
ctypedef shared_ptr[AbsSmtSolver] SmtSolver
ctypedef vector[Sort] SortVec
ctypedef vector[Term] TermVec
# ctypedef unordered_map[Term, Term] UnorderedTermMap


cdef extern from "<iostream>" namespace "std":
    cdef cppclass ostream:
        pass
    ostream cout


cdef extern from "sort.h" namespace "smt":
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


cdef extern from "ops.h" namespace "smt":
    cdef cppclass Op:
        Op() except +
        Op(PrimOp o) except +
        Op(PrimOp o, uint64_t idx0) except +
        Op(PrimOp o, uint64_t idx0, uint64_t idx1) except +
        string to_string() except +


# TODO See if we can combine with above cdef extern
cdef extern from "ops.h" namespace "smt":
    bint operator==(Op op1, Op op2) except +
    bint operator!=(Op op1, Op op2) except +
    ostream& operator<<(ostream & output, const Op o) except +


cdef extern from "term.h" namespace "smt":
    cdef cppclass UnorderedTermMap:
        void emplace(Term k, Term v) except +

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
cdef extern from "term.h" namespace "smt":
    bint operator==(const Term& t1, const Term& t2) except +
    bint operator!=(const Term& t1, const Term& t2) except +
    ostream& operator<<(ostream& output, const Term t) except +


cdef extern from "result.h" namespace "smt":
    cdef cppclass Result:
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
        void assert_formula(const Term & t) except +
        Result check_sat() except +
        Result check_sat_assuming(const TermVec & assumptions) except +
        void push(uint64_t num) except +
        void pop(uint64_t num) except +
        Term get_value(Term& t) except +
        Sort make_sort(const string name, uint64_t arity) except +
        Sort make_sort(const SortKind sk) except +
        Sort make_sort(const SortKind sk, uint64_t size) except +
        Sort make_sort(const SortKind sk, const Sort & sort1) except +
        Sort make_sort(const SortKind sk, const Sort & sort1, const Sort & sort2) except +
        Sort make_sort(const SortKind sk, const Sort & sort1, const Sort & sort2, const Sort & sort3) except +
        Sort make_sort(const SortKind sk, const SortVec & sorts) except +
        Term make_term(bint b) except +
        Term make_term(int64_t i, const Sort & sort) except +
        Term make_term(const string val, const Sort & sort) except +
        Term make_term(const string val, const Sort & sort, uint64_t base) except +
        Term make_term(const Term & val, const Sort & sort) except +
        Term make_symbol(const string name, const Sort & sort) except +
        Term make_term(const Op op, const Term & t) except +
        Term make_term(const Op op, const Term & t0, const Term & t1) except +
        Term make_term(const Op op, const Term & t0, const Term & t1, const Term & t2) except +
        Term make_term(const Op op, const TermVec & terms) except +
        void reset() except +
        void reset_assertions() except +
        Term substitute(const Term term, const UnorderedTermMap & substitution_map) except +


# TODO autogenerate this
cdef extern from "msat_factory.h" namespace "smt::MsatSolverFactory":
    SmtSolver create() except +
