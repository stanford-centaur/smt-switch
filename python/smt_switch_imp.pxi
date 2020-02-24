from cython.operator cimport dereference as dref
from libcpp.string cimport string
from libcpp.unordered_map cimport unordered_map
from libcpp.vector cimport vector

from smt_switch_imp cimport Op as c_Op
from smt_switch_imp cimport Result as c_Result
from smt_switch_imp cimport c_SmtSolver
from smt_switch_imp cimport c_Sort
from smt_switch_imp cimport c_SortVec
from smt_switch_imp cimport c_Term
from smt_switch_imp cimport c_TermVec
from smt_switch_imp cimport UnorderedTermMap as c_UnorderedTermMap
from smt_switch_imp cimport TermIter as c_TermIter

from enums cimport SortKind as c_SortKind
from enums cimport PrimOp as c_PrimOp
# PrimOp, SortKind classes are defined at this scope
# because enums.pxi is inlined before this


cdef class Op:
    cdef c_Op op
    def __cinit__(self, prim_op=None, idx0=None, idx1=None):
        if isinstance(prim_op, PrimOp):
            if idx0 is None:
                self.op = c_Op((<PrimOp?> prim_op).po)
            elif idx1 is None:
                self.op = c_Op((<PrimOp?> prim_op).po, <int?> idx0)
            else:
                self.op = c_Op((<PrimOp?> prim_op).po, <int?> idx0, <int?> idx1)
        else:
            self.op = c_Op()

    @property
    def prim_op(self):
        cdef PrimOp po = PrimOp()
        po.po = self.op.prim_op
        return po

    @property
    def num_idx(self):
        return self.op.num_idx

    @property
    def idx0(self):
        return self.op.idx0

    @property
    def idx1(self):
        return self.op.idx1

    def __bool__(self):
        return not self.op.is_null()

    def __str__(self):
        return self.op.to_string().decode()

    def __repr__(self):
        return str(self)

    def __eq__(self, Op other):
        return self.op == other.op

    def __ne__(self, Op other):
        return self.op != other.op

cdef class Result:
    cdef c_Result cr
    def __cinit__(self):
        pass

    def is_sat(self):
        return self.cr.is_sat()

    def is_unsat(self):
        return self.cr.is_unsat()

    def is_unknown(self):
        return self.cr.is_unknown()

    def is_null(self):
        return self.cr.is_null()

    def __str__(self):
        return self.cr.to_string().decode()

    def __repr__(self):
        return str(self)


cdef class Sort:
    cdef c_Sort cs
    cdef SmtSolver _solver
    def __cinit__(self):
        pass

    def __init__(self, SmtSolver solver):
        # some backends require the solver to be present for destruction
        # of sorts and terms
        # Python doesn't know this and will garbage collect in the wrong order
        # Keeping a reference to the solver prevents this
        self._solver = solver

    def get_width(self):
        return dref(self.cs).get_width()

    def get_indexsort(self):
        cdef Sort s = Sort(self._solver)
        s.cs = dref(self.cs).get_indexsort()
        return s

    def get_elemsort(self):
        cdef Sort s = Sort(self._solver)
        s.cs = dref(self.cs).get_elemsort()
        return s

    def get_domain_sorts(self):
        sorts = []

        cdef Sort s = Sort(self._solver)
        for cs in dref(self.cs).get_domain_sorts():
            s.cs = cs
            sorts.append(s)

        return sorts

    def get_codomain_sort(self):
        cdef Sort s = Sort(self._solver)
        s.cs = dref(self.cs).get_codomain_sort()
        return s

    def get_sort_kind(self):
        cdef SortKind sk = SortKind()
        sk.sk = dref(self.cs).get_sort_kind()
        return sk

    def __eq__(self, Sort other):
        return self.cs == other.cs

    def __ne__(self, Sort other):
        return self.cs != other.cs

    def __str__(self):
        return dref(self.cs).to_string().decode()

    def __repr__(self):
        return str(self)

    def __hash__(self):
        return dref(self.cs).hash()


cdef class Term:
    cdef c_Term ct
    cdef SmtSolver _solver
    def __cinit__(self):
        pass

    def __init__(self, SmtSolver solver):
        # some backends require the solver to be present for destruction
        # of sorts and terms
        # Python doesn't know this and will garbage collect in the wrong order
        # Keeping a reference to the solver prevents this
        self._solver = solver

    def get_op(self):
        cdef Op o = Op()
        o.op = dref(self.ct).get_op()
        return o

    def get_sort(self):
        cdef Sort s = Sort(self._solver)
        s.cs = dref(self.ct).get_sort()
        return s

    def is_symbolic_const(self):
        return dref(self.ct).is_symbolic_const()

    def is_value(self):
        return dref(self.ct).is_value()

    def __int__(self):
        val = dref(self.ct).to_string().decode()
        s = self.get_sort()
        sk = s.get_sort_kind()

        try:
            if sk == BV:
                if val[:2] == '#b':
                    return int(val[2:], 2)
                elif val[:5] == '(_ bv':
                    val = val[5:]
                    val = val[:val.find(" ")]
                    return int(val)
                else:
                    raise ValueError("Unable to interpret % as int"%self)
            elif sk == INT:
                if val[:2] == '(-':
                    val = val[3:-1]
                    val = "-" + val
                return int(val)
            else:
                raise ValueError("Unable to interpret % as int"%self)
        except:
            raise ValueError("Unable to interpret % as int"%self)


    def __str__(self):
        return dref(self.ct).to_string().decode()

    def __repr__(self):
        return str(self)

    def __hash__(self):
        return dref(self.ct).hash()

    def __eq__(self, Term other):
        return self.ct == other.ct

    def __ne__(self, Term other):
        return self.ct != other.ct

    def __iter__(self):
        for ci in dref(self.ct):
            t = Term(self._solver)
            t.ct = ci
            yield t


cdef class SmtSolver:
    cdef c_SmtSolver css
    def __cinit__(self):
        pass

    def set_opt(self, str option, str value):
        dref(self.css).set_opt(option.encode(), value.encode())

    def set_logic(self, str logic):
        dref(self.css).set_logic(logic.encode())

    def assert_formula(self, Term t):
        dref(self.css).assert_formula(t.ct)

    def check_sat(self):
        cdef Result r = Result()
        r.cr = dref(self.css).check_sat()
        return r

    def check_sat_assuming(self, assumptions):
        cdef c_TermVec ctv
        cdef Result r = Result()
        for a in assumptions:
            if not isinstance(a, Term):
                raise ValueError("Expecting a Term but got {}")
            ctv.push_back((<Term> a).ct)
        dref(self.css).check_sat_assuming(ctv)
        return r

    def push(self, int num=1):
        dref(self.css).push(num)

    def pop(self, int num=1):
        dref(self.css).pop(num)

    def get_value(self, Term t):
        cdef Term term = Term(self)
        term.ct = dref(self.css).get_value(t.ct)
        return term

    def make_sort(self, arg0, arg1=None, arg2=None, arg3=None):
        cdef Sort s = Sort(self)
        cdef c_SortKind sk
        cdef c_SortVec csv

        if isinstance(arg0, str):
            s.cs = dref(self.css).make_sort(<const string> arg0.encode(), <int?> arg1)
        elif isinstance(arg0, SortKind):
            sk = (<SortKind> arg0).sk
            if arg1 is None:
                s.cs = dref(self.css).make_sort(sk)
            elif isinstance(arg1, int) and arg2 is None:
                s.cs = dref(self.css).make_sort(sk, <int> arg1)
            elif isinstance(arg1, Sort) and arg2 is None:
                s.cs = dref(self.css).make_sort(sk, (<Sort> arg1).cs)
            elif isinstance(arg1, list) and arg2 is None:
                for a in arg1:
                    csv.push_back((<Sort?> a).cs)
                s.cs = dref(self.css).make_sort(sk, csv)
            elif arg3 is None:
                s.cs = dref(self.css).make_sort(sk, (<Sort?> arg1).cs, (<Sort?> arg2).cs)
            elif arg3 is not None:
                s.cs = dref(self.css).make_sort(sk, (<Sort?> arg1).cs,
                                                    (<Sort?> arg2).cs,
                                                    (<Sort?> arg3).cs)
            else:
                raise ValueError("Cannot find matching function for {}".format([type(a)
                                                                                for a in
                                                                                [arg0, arg1, arg2, arg3]]))
        else:
            raise ValueError("Cannot find matching function for {}".format([type(a)
                                                                            for a in
                                                                            [arg0, arg1, arg2, arg3]]))
        return s

    def make_term(self, arg0, arg1=None, arg2=None, arg3=None):
        cdef Term term = Term(self)
        cdef c_TermVec ctv

        if isinstance(arg0, PrimOp):
            arg0 = Op(arg0)

        if isinstance(arg0, Op):
            if not arg0:
                raise ValueError("Got a null Op in make_term")

            if arg2 is None:
                term.ct = dref(self.css).make_term((<Op> arg0).op, (<Term?> arg1).ct)
            elif arg3 is None:
                term.ct = dref(self.css).make_term((<Op> arg0).op, (<Term?> arg1).ct, (<Term?> arg2).ct)
            elif arg3 is not None:
                term.ct = dref(self.css).make_term((<Op> arg0).op, (<Term?> arg1).ct, (<Term?> arg2).ct, (<Term?> arg3).ct)
            elif isinstance(arg1, list):
                for a in arg1:
                    ctv.push_back((<Term?> a).ct)
                term.ct = dref(self.css).make_term((<Op> arg0).op, ctv)
            else:
                raise ValueError("Expecting Op and Terms but got {}".format([type(a)
                                                                             for a in [arg0, arg1, arg2, arg3]]))
        elif isinstance(arg0, str) and isinstance(arg1, Sort):
            if arg2 is None:
                term.ct = dref(self.css).make_term(<const string> arg0.encode(), (<Sort> arg1).cs)
            else:
                term.ct = dref(self.css).make_term(<const string> arg0.encode(),
                                                   (<Sort> arg1).cs,
                                                    <int?> arg2)
        elif isinstance(arg0, int) and isinstance(arg1, Sort) and arg2 is None:
            term.ct = dref(self.css).make_term(<int> arg0, (<Sort> arg1).cs)
        elif isinstance(arg0, bool) and arg1 is None:
            term.ct = dref(self.css).make_term(<bint> arg0)
        elif isinstance(arg0, Term) and isinstance(arg1, Sort) and arg2 is None:
            term.ct = dref(self.css).make_term((<Term> arg0).ct, (<Sort> arg1).cs)
        else:
            raise ValueError("Couldn't find matching function for {}".format([type(a)
                                                                             for a in [arg0, arg1, arg2, arg3]]))
        return term

    def make_symbol(self, str name, Sort sort):
        cdef Term term = Term(self)
        term.ct = dref(self.css).make_symbol(name.encode(), sort.cs)
        return term

    def reset(self):
        dref(self.css).reset()

    def reset_assertions(self):
        dref(self.css).reset_assertions()

    def substitute(self, Term t, dict substitution_map):
        cdef Term term = Term(self)
        cdef c_UnorderedTermMap utm

        for k, v in substitution_map.items():
            utm.emplace((<Term?> k).ct, (<Term?> v).ct)

        term.ct = dref(self.css).substitute(t.ct, utm)
        return term
