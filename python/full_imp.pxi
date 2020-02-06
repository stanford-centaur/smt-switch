from cython.operator cimport dereference as dref
from libcpp.string cimport string
from libcpp.unordered_map cimport unordered_map
from libcpp.vector cimport vector

from full_imp cimport create
from full_imp cimport Op as c_Op
from full_imp cimport Result as c_Result
from full_imp cimport SmtSolver as c_SmtSolver
from full_imp cimport Sort as c_Sort
from full_imp cimport SortVec as c_SortVec
from full_imp cimport Term as c_Term
from full_imp cimport TermVec as c_TermVec
from full_imp cimport UnorderedTermMap as c_UnorderedTermMap
from full_imp cimport TermIter as c_TermIter

from enums cimport SortKind as c_SortKind
# PrimOp, SortKind classes are defined at this scope
# because enums.pxi is inlined before this

cdef class Op:
    cdef c_Op op
    def __cinit__(self, PrimOp o, idx0=None, idx1=None):
        if idx0 is None:
            self.op = c_Op(o.po)
        elif idx1 is None:
            if not isinstance(idx0, int):
                raise ValueError("Expecting int but got {}".format(type(idx0)))
            self.op = c_Op(o.po, <int> idx0)
        else:
            if not isinstance(idx0, int) or not isinstance(idx1, int):
                raise ValueError("Expecting <int, int> but got <{}, {}>".format(type(idx0),
                                                                                type(idx1)))
            self.op = c_Op(o.po, <int> idx0, <int> idx1)

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
    def __cinit__(self):
        pass

    def get_width(self):
        return dref(self.cs).get_width()

    def get_indexsort(self):
        cdef Sort s = Sort()
        s.cs = dref(self.cs).get_indexsort()
        return s

    def get_elemsort(self):
        cdef Sort s = Sort()
        s.cs = dref(self.cs).get_elemsort()
        return s

    def get_domain_sorts(self):
        sorts = []

        cdef Sort s = Sort()
        for cs in dref(self.cs).get_domain_sorts():
            s.cs = cs
            sorts.append(s)

        return sorts

    def get_codomain_sort(self):
        cdef Sort s = Sort()
        s.cs = dref(self.cs).get_codomain_sort()
        return s

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
    def __cinit__(self):
        pass

    def get_op(self):
        # Technically not supporting the empty constructor
        # TODO check that this actually works
        cdef Op o = Op()
        o.op = dref(self.ct).get_op()
        return o

    def get_sort(self):
        cdef Sort s = Sort()
        s.cs = dref(self.ct).get_sort()
        return s

    def is_symbolic_const(self):
        return dref(self.ct).is_symbolic_const()

    def is_value(self):
        return dref(self.ct).is_value()

    def __int__(self):
        return dref(self.ct).to_int()

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
            t = Term()
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

    def push(self, int num):
        dref(self.css).push(num)

    def pop(self, int num):
        dref(self.css).pop(num)

    def get_value(self, Term t):
        cdef Term term = Term()
        term.ct = dref(self.css).get_value(t.ct)
        return term

    def make_sort(self, arg0, arg1=None, arg2=None, arg3=None):
        cdef Sort s = Sort()
        cdef c_SortKind sk
        cdef c_SortVec csv

        if isinstance(arg0, str):
            if not isinstance(arg1, int):
                raise ValueError("Expecting second argument to be int but got {}".format(type(arg1)))
            s.cs = dref(self.css).make_sort(<const string> arg0.encode(), <int> arg1)
        elif isinstance(arg0, SortKind):
            sk = (<SortKind> arg0).sk
            if isinstance(arg1, int):
                s.cs = dref(self.css).make_sort(sk, <int> arg1)
            elif isinstance(arg1, Sort) and arg2 is None:
                s.cs = dref(self.css).make_sort(sk, (<Sort> arg1).cs)
            elif [type(arg1), type(arg2)] == [Sort, Sort] and arg3 is None:
                s.cs = dref(self.css).make_sort(sk, (<Sort> arg1).cs, (<Sort> arg2).cs)
            elif [type(arg1), type(arg2), type(arg3)] == [Sort, Sort, Sort]:
                s.cs = dref(self.css).make_sort(sk, (<Sort> arg1).cs,
                                                    (<Sort> arg2).cs,
                                                    (<Sort> arg3).cs)
            elif isinstance(arg1, list):
                for a in arg1:
                    if not isinstance(a, Sort):
                        raise ValueError("Expecting a sort but got {}".format(type(a)))
                    csv.push_back((<Sort> a).cs)
                s.cs = dref(self.css).make_sort(sk, csv)
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
        cdef Term term = Term()
        cdef c_TermVec ctv

        if isinstance(arg0, PrimOp):
            arg0 = Op(arg0)

        if isinstance(arg0, Op):
            if isinstance(arg1, Term) and arg2 is None:
                term.ct = dref(self.css).make_term((<Op> arg0).op, (<Term> arg1).ct)
            elif [type(arg1), type(arg2)] == [Term, Term] and arg3 is None:
                term.ct = dref(self.css).make_term((<Op> arg0).op, (<Term> arg1).ct, (<Term> arg2).ct)
            elif [type(arg1), type(arg2), type(arg3)] == [Term, Term, Term]:
                term.ct = dref(self.css).make_term((<Op> arg0).op, (<Term> arg1).ct, (<Term> arg2).ct, (<Term> arg3).ct)
            elif isinstance(arg1, list):
                for a in arg1:
                    if not isinstance(a, Term):
                        raise ValueError("Expecting a Term but got {}".format(type(a)))
                    ctv.push_back((<Term> a).ct)
                term.ct = dref(self.css).make_term((<Op> arg0).op, ctv)
            else:
                raise ValueError("Expecting Op and Terms but got {}".format([type(a)
                                                                             for a in [arg0, arg1, arg2, arg3]]))
        elif isinstance(arg0, str) and isinstance(arg1, Sort):
            if arg2 is None:
                term.ct = dref(self.css).make_term(<const string> arg0.encode(), (<Sort> arg1).cs)
            else:
                if not isinstance(arg2, int):
                    raise ValueError("Expecting an int but got {}".format(type(arg2)))
                term.ct = dref(self.css).make_term(<const string> arg0.encode(),
                                                   (<Sort> arg1).cs,
                                                   <int> arg2)
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
        cdef Term term = Term()
        term.ct = dref(self.css).make_symbol(name.encode(), sort.cs)
        return term

    def reset(self):
        dref(self.css).reset()

    def reset_assertions(self):
        dref(self.css).reset_assertions()

    def substitute(self, Term t, dict substitution_map):
        cdef Term term = Term()
        cdef c_UnorderedTermMap utm

        for k, v in substitution_map.items():
            if not isinstance(k, Term) or not isinstance(v, Term):
                raise ValueError("Expecting Terms but got {}".format([type(k), type(v)]))
            utm.emplace((<Term> k).ct, (<Term> v).ct)

        term.ct = dref(self.css).substitute(t.ct, utm)
        return term


def create_msat_solver():
    cdef SmtSolver solver = SmtSolver()
    solver.css = create()
    return solver
