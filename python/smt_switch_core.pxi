from abc import ABC, abstractmethod

from cython.operator cimport dereference as dref
from libcpp.string cimport string
from libcpp.unordered_map cimport unordered_map
from libcpp.vector cimport vector

from smt_switch_core cimport (
    c_Op,
    c_Result,
    c_SmtSolver,
    c_Sort,
    c_SortVec,
    c_SortingNetwork,
    c_Term,
    c_TermIter,
    c_TermVec,
    c_UnorderedTermMap,
    c_UnorderedTermSet
)

from smt_switch_core cimport get_free_symbolic_consts as c_get_free_symbolic_consts
from smt_switch_core cimport get_free_symbols as c_get_free_symbols
from smt_switch_core cimport op_partition as c_op_partition
from smt_switch_core cimport conjunctive_partition as c_conjunctive_partition

from smt_switch_enums cimport (
    c_SortKind,
    c_ARRAY,
    c_BOOL,
    c_BV,
    c_INT,
    c_REAL,
    c_FUNCTION,
)
from smt_switch_enums cimport c_PrimOp


cdef class Op:
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
        # look up the canonical object
        return int2primop[(<int> self.op.prim_op)]

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

    def __eq__(self, other):
        if isinstance(other, Op):
            return self.op == (<Op> other).op
        elif isinstance(other, PrimOp):
            return self == Op(other)
        else:
            raise ValueError("Unexpected comparison between Op and {}".format(type(other)))

    def __ne__(self, other):
        if isinstance(other, Op):
            return self.op != (<Op> other).op
        elif isinstance(other, PrimOp):
            return self != Op(other)
        else:
            raise ValueError("Unexpected comparison between Op and {}".format(type(other)))

cdef class Result:
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

    def get_explanation(self):
        return self.cr.get_explanation()

    def __str__(self):
        return self.cr.to_string().decode()

    def __repr__(self):
        return str(self)


cdef class Sort:
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

        for cs in dref(self.cs).get_domain_sorts():
            s = Sort(self._solver)
            s.cs = cs
            sorts.append(s)

        return sorts

    def get_codomain_sort(self):
        cdef Sort s = Sort(self._solver)
        s.cs = dref(self.cs).get_codomain_sort()
        return s

    def get_sort_kind(self):
        # look up canonical SortKind object
        return int2sortkind[(<int> dref(self.cs).get_sort_kind())]

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
        '''
        Interpret a term as an integer.

        Note: bit-vectors are always treated as unsigned integers.
        '''
        val = dref(self.ct).to_string().decode()
        s = self.get_sort()
        sk = s.get_sort_kind()

        try:
            if sk == BV:
                if val[-1] == 's':
                    # notation from z3 for signed bv
                    # we're choosing to always interpret
                    # the bitvector as unsigned
                    # users can convert if needed
                    val = val[:-1]

                if val[:2] == '#b':
                    return int(val[2:], 2)
                elif val[:2] == '#x':
                    return int(val[2:], 16)
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

    def __bool__(self):
        cdef c_Sort csort = dref(self.ct).get_sort()
        cdef c_Sort cboolsort = dref(self._solver.css).make_sort(c_BOOL)

        if csort != cboolsort or not dref(self.ct).is_value():
            raise ValueError("Cannot call bool on {}".format(str(self)))

        cdef Term t = self._solver.make_term(True)

        return (self.ct == t.ct)

    def __iter__(self):
        for ci in dref(self.ct):
            t = Term(self._solver)
            t.ct = ci
            yield t


cdef class SmtSolver:
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
        r.cr = dref(self.css).check_sat_assuming(ctv)
        return r

    def push(self, int num=1):
        dref(self.css).push(num)

    def pop(self, int num=1):
        dref(self.css).pop(num)

    def get_value(self, Term t):
        cdef Term term = Term(self)
        term.ct = dref(self.css).get_value(t.ct)
        return term

    def get_unsat_assumptions(self):
        unsat_assumptions = set()
        cdef c_UnorderedTermSet cts
        dref(self.css).get_unsat_assumptions(cts)
        for l in cts:
            term = Term(self)
            term.ct = l
            unsat_assumptions.add(term)
        return unsat_assumptions

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

    def make_term(self, op_or_val, *args):
        cdef Term term = Term(self)
        cdef c_TermVec ctv

        if isinstance(op_or_val, PrimOp):
            op_or_val = Op(op_or_val)

        # expand a list argument
        if len(args) > 0:
            if (isinstance(args[0], list) and len(args) > 1) or \
               any([isinstance(a, list) for a in args[1:]]):
                raise ValueError("Cannot call make_term with signature {}".format([type(a) for a in args]))
            elif isinstance(args[0], list):
                # expand arguments in list to be args
                args = args[0]

        if isinstance(op_or_val, Op):
            if not op_or_val:
                raise ValueError("Got a null Op in make_term")

            if not args:
                raise ValueError("Can't call make_term with an Op ({}) and no arguments".format(op_or_val))

            for a in args:
                ctv.push_back((<Term?> a).ct)
            term.ct = dref(self.css).make_term((<Op> op_or_val).op, ctv)
        elif isinstance(op_or_val, bool) and len(args) == 0:
            term.ct = dref(self.css).make_term(<bint> op_or_val)
        elif isinstance(op_or_val, str) and len(args) == 1 and isinstance(args[0], Sort):
            term.ct = dref(self.css).make_term(<const string> op_or_val.encode(), (<Sort> args[0]).cs)
        elif isinstance(op_or_val, str) and len(args) == 2 and isinstance(args[0], Sort):
            term.ct = dref(self.css).make_term(<const string> op_or_val.encode(),
                                               (<Sort> args[0]).cs,
                                               <int?> args[1])
        elif isinstance(op_or_val, int) and len(args) == 1 and isinstance(args[0], Sort):
            # always use the string representation of integers (to handle large ints)
            term.ct = dref(self.css).make_term((<const string?> str(op_or_val).encode()), (<Sort> args[0]).cs)
        elif isinstance(op_or_val, Term) and len(args) == 1 and isinstance(args[0], Sort):
            # this is for creating a constant array
            term.ct = dref(self.css).make_term((<Term?> op_or_val).ct, (<Sort?> args[0]).cs)
        else:
            raise ValueError("Couldn't find matching function for {}".format([type(a)
                                                                              for a in [op_or_val] + args]))
        return term

    def make_symbol(self, str name, Sort sort):
        cdef Term term = Term(self)
        term.ct = dref(self.css).make_symbol(name.encode(), sort.cs)
        return term

    def make_param(self, str name, Sort sort):
        cdef Term term = Term(self)
        term.ct = dref(self.css).make_param(name.encode(), sort.cs)
        return term

    def reset(self):
        dref(self.css).reset()

    def reset_assertions(self):
        dref(self.css).reset_assertions()

    def substitute(self, Term t, dict substitution_map):
        cdef Term term = Term(self)
        cdef c_UnorderedTermMap utm

        for k, v in substitution_map.items():
            utm[(<Term?> k).ct] = (<Term?> v).ct

        term.ct = dref(self.css).substitute(t.ct, utm)
        return term

    def dump_smt2(self, str filename):
        dref(self.css).dump_smt2(filename.encode());

    def get_interpolant(self, Term A, Term B):
        '''
        Get an interpolant for A, and B. Note: this will throw an exception if called
        on a solver that was not created with create_<solver>_interpolator

        returns None if the interpolant could not be computed or the query
                was satisfiable
        '''
        cdef c_Term cI
        cdef Term I = Term(self)

        res = dref(self.css).get_interpolant(A.ct, B.ct, cI)
        if not res.is_unsat():
            return None
        else:
            I.ct = cI
            return I


cdef class SortingNetwork:
    def __cinit__(self, SmtSolver solver):
        self.csn = new c_SortingNetwork(solver.css)
        self._solver = solver

    def __dealloc__(self):
        del self.csn

    def sorting_network(self, list unsorted):
        cdef c_TermVec ctv
        for u in unsorted:
            ctv.push_back((<Term?> u).ct)

        res = []
        for r in dref(self.csn).sorting_network(ctv):
            t = Term(self._solver)
            t.ct = r
            res.append(t)
        return res


# Utils

def get_free_symbolic_consts(Term term):
    '''
    Return a set of all the free symbolic constants (e.g. excludes function symbols) in the provided term.
    '''

    cdef c_UnorderedTermSet out_symbols
    c_get_free_symbolic_consts(term.ct, out_symbols)

    python_out_set = set()
    for s in out_symbols:
        t = Term(term._solver)
        t.ct = s
        python_out_set.add(t)

    return python_out_set


def get_free_symbols(Term term):
    '''
    Return a set of all the free symbols in the provided term.
    '''

    cdef c_UnorderedTermSet out_symbols
    c_get_free_symbols(term.ct, out_symbols)

    python_out_set = set()
    for s in out_symbols:
        t = Term(term._solver)
        t.ct = s
        python_out_set.add(t)

    return python_out_set

def op_partition(PrimOp po, Term term):
    '''
    Returns a list of nested terms partition by operator po

    Example
      op_partition(Plus, solver.make_term(Plus, a, solver.make_term(Plus, b, c)))
      returns: [a, b, c]
    '''

    cdef c_TermVec out
    c_op_partition(po.po, term.ct, out)

    python_out_list = []
    for s in out:
        t = Term(term._solver)
        t.ct = s
        python_out_list.append(t)

    return python_out_list

def conjunctive_partition(Term term, bint include_bvand=False):
    '''
    Calls op_partition for And. Also has an option to include BVAnd.
    '''

    cdef c_TermVec out
    c_conjunctive_partition(term.ct, out, include_bvand)

    python_out_list = []
    for s in out:
        t = Term(term._solver)
        t.ct = s
        python_out_list.append(t)

    return python_out_list

class TermDagVisitor(ABC):
    def __init__(self):
        pass

    def walk_dag(self, term):
        '''
        Walks through all the subterms in the DAG of term
        '''

        to_visit = [term]
        visited  = set()
        cache    = dict()

        while to_visit:
            t = to_visit.pop()

            if t in visited:
                new_children = [cache[tt] for tt in t]
                cache[t] = self.visit_term(t, new_children)
            else:
                visited.add(t)
                to_visit.append(t)
                for tt in t:
                    to_visit.append(tt)

        return cache[term]

    @abstractmethod
    def visit_term(self, term, new_children):
        '''
        Visit a particular term (in postorder).
        Derived classes should override this method.
        @param term the smt-switch term to visit
        @param new_children the previously visited children
        @return updated/translated term
        '''

        raise NotImplementedError("visit_term not implemented in base class")


# example derived class for TermDagVisitor
class IdentityVisitor(TermDagVisitor):
    def __init__(self, solver):
        self._solver = solver

    def visit_term(self, term, new_children):
        op = term.get_op()
        if op:
            return self._solver.make_term(op, new_children)
        elif new_children:
            # constant array case
            return term
        else:
            # symbol / value / parameter case
            return term
