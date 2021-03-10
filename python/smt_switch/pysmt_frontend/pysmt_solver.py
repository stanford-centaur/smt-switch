from collections import ChainMap
import fractions
import functools as ft
import gc
import itertools as it
import operator

import smt_switch as ss


from pysmt.exceptions import (UndefinedLogicError,
        SolverReturnedUnknownResultError, ConvertExpressionError, PysmtValueError)
from pysmt.solvers.solver import (IncrementalTrackingSolver, UnsatCoreSolver,
                                  Converter, SolverOptions)
from pysmt.solvers.smtlib import SmtLibBasicSolver, SmtLibIgnoreMixin
from pysmt.solvers.eager import EagerModel
from pysmt.walkers import DagWalker
from pysmt.decorators import clear_pending_pop, catch_conversion_error
from pysmt.logics import get_logic, SMTLIB2_LOGICS
from pysmt import typing as pysmt_types


SWITCH_SOLVERS = {}

class SwitchOptions(SolverOptions):
    def __call__(self, solver):
        if self.generate_models:
            solver.solver.set_opt('produce-models', 'true')
        if self.incremental:
            solver.solver.set_opt('incremental', 'true')

        for k, v in self.solver_options.items():
            try:
                solver.solver.set_opt(k, v)
            except:
                raise PysmtValueError(f"Error setting the option '{k}={v}'")


def _parse_real(s):
    def _parse(it):
        tree = []
        num = []
        for c in it:
            if c.isdigit():
                num.append(c)
                continue
            elif num:
                tree.append(int(''.join(num)))
                num = []

            if c == ')':
                break
            elif c == ' ':
                continue
            elif c == '(':
                tree.append(_parse(it))
            elif c == '-':
                tree.append(operator.neg)
            elif c == '/':
                tree.append(fractions.Fraction)
            else:
                raise ValueError()

        if num:
            tree.append(int(''.join(num)))

        assert tree
        if len(tree) == 1:
            assert isinstance(tree[0], (int, fractions.Fraction))
            return tree[0]
        else:
            return tree[0](*tree[1:])

    return _parse(iter(repr(s)))


class _SwitchSolver(IncrementalTrackingSolver,
                   SmtLibBasicSolver,
                   SmtLibIgnoreMixin):
    OptionsClass = SwitchOptions

    def __init__(self, environment, logic, **options):
        IncrementalTrackingSolver.__init__(self,
                        environment=environment,
                        logic=logic,
                        **options)

        self.solver = self._create_solver()
        self.options(self)
        self.mgr = environment.formula_manager
        self.converter = SwitchConverter(environment,  self.solver, self.mgr)

    def get_model(self):
        assignment = {}
        for s in self.converter.declared_vars:
            v = self.get_value(s)
            assignment[s] = v
        return EagerModel(assignment=assignment, environment=self.environment)

    def get_value(self, item):
        self._assert_no_function_type(item)
        sort = item.get_type()
        c_item = self.converter.convert(item)
        val = self.solver.get_value(c_item)
        # HACK because smt-switch sometimes loses sorts
        # we can't use back
        # should be: `r_val = self.converter.back(val)`
        r_val = self.converter.back_walker._convert_value(val, sort)
        assert r_val.get_type() == sort
        return r_val

    @clear_pending_pop
    def _reset_assertions(self):
        self.solver.reset_assertions()

    @clear_pending_pop
    def _add_assertion(self, formula, named=None):
        self._assert_is_boolean(formula)
        term = self.converter.convert(formula)
        self.solver.assert_formula(term)

    @clear_pending_pop
    def _solve(self, assumptions=None):
        if assumptions is None:
            assumptions = ()

        bool_ass = []
        other_ass = []
        for x in assumptions:
            if x.is_literal():
                bool_ass.append(self.converter.convert(x))
            else:
                other_ass.append(x)

        if other_ass:
            self.push()
            self.add_assertion(self.mgr.And(other_ass))
            self.pending_pop = True

        if bool_ass:
            res = self.solver.check_sat_assuming(bool_ass)
        else:
            res = self.solver.check_sat()

        if res.is_sat():
            return True
        elif res.is_unsat():
            return False
        else:
            raise SolverReturnedUnknownResultError()

    @clear_pending_pop
    def _push(self, levels=1):
        self.solver.push(levels)

    @clear_pending_pop
    def _pop(self, levels=1):
        self.solver.pop(levels)

    def _exit(self):
        del self.solver


def _build_logics(logics_params):
    logics = []
    for params in it.product(*logics_params.values()):
        args = dict(zip(logics_params.keys(), params))
        try:
            logic = get_logic(**args)
        except UndefinedLogicError:
            pass
        else:
            if logic in SMTLIB2_LOGICS:
                logics.append(logic)

    return logics


if 'btor' in  ss.solvers:
    logics_params = dict(
        quantifier_free=[True],
        arrays=[True, False],
        bit_vectors=[True, False],
        uninterpreted=[True, False],
    )


    class SwitchBtor(_SwitchSolver):
        LOGICS = _build_logics(logics_params)
        _create_solver = ft.partial(ss.create_btor_solver, False)

        @clear_pending_pop
        def _reset_assertions(self):
            self.solver = self._create_solver()
            self.converter = SwitchConverter(self.environment,  self.solver, self.mgr)
            self.options(self)


    SWITCH_SOLVERS['btor'] = SwitchBtor


if 'msat' in ss.solvers:
    logics_params = dict(
        quantifier_free=[True],
        arrays=[True, False],
        bit_vectors=[True, False],
        uninterpreted=[True, False],
        integer_arithmetic=[True, False],
        integer_difference=[True, False],
        real_arithmetic=[True, False],
        real_difference=[True, False],
        linear=[True],
    )

    class SwitchMsat(_SwitchSolver):
        LOGICS = _build_logics(logics_params)
        _create_solver = ft.partial(ss.create_msat_solver, False)

    SWITCH_SOLVERS['msat'] = SwitchMsat

if 'cvc4' in ss.solvers:
    logics_params = dict(
        quantifier_free=[True],
        arrays=[True, False],
        bit_vectors=[True, False],
        uninterpreted=[True, False],
        integer_arithmetic=[True, False],
        integer_difference=[True, False],
        real_arithmetic=[True, False],
        real_difference=[True, False],
        linear=[True],
    )

    class SwitchCVC4(_SwitchSolver):
        LOGICS = _build_logics(logics_params)
        _create_solver = ft.partial(ss.create_cvc4_solver, False)

        def _exit(self):
            super()._exit()
            # ensure prompt collection of the solver object
            # to avoid heisenbug
            gc.collect()

    SWITCH_SOLVERS['cvc4'] = SwitchCVC4


def check_args(cmp, n):
    def wrapper(f):
        @ft.wraps(f)
        def walk_op(self, formula, args, **kwargs):
            if not cmp(len(args), n):
                raise ConvertExpressionError('Incorrect number of arguments')
            return f(self, formula, args, **kwargs)
        return walk_op
    return wrapper


def make_walk_nary(n, primop):
    @check_args(operator.eq, n)
    def walk_op(self, formula, args, **kwargs):
        res = self.make_term(primop, *args)
        return res
    return walk_op


make_walk_unary = ft.partial(make_walk_nary, 1)
make_walk_binary = ft.partial(make_walk_nary, 2)


def make_walk_variadic(n, primop):
    @check_args(operator.ge, n)
    def walk_op(self, formula, args, **kwargs):
        builder = ft.partial(self.make_term, primop)
        res = ft.reduce(builder, args)
        return res
    return walk_op


class SwitchConverter(Converter, DagWalker):
    def __init__(self, environment, solver, mgr):
        DagWalker.__init__(self, environment)
        self.solver = solver
        self.make_term = solver.make_term
        self.make_symbol = solver.make_symbol
        self.make_sort = solver.make_sort
        self.declared_funs = fs = {}
        self.declared_vars = vs = {}
        self.declared_syms = ChainMap(vs, fs)
        self.declared_sorts = {}
        self.back_walker = BackVisitor(mgr)

    @catch_conversion_error
    def convert(self, formula):
        return self.walk(formula)

    def back(self, expr):
        return self.back_walker.walk_dag(expr)

    def _convert_sort(self, sort):
        try:
            return self.declared_sorts[sort]
        except KeyError:
            pass

        if sort.is_array_type():
            c_sort = self.make_sort(
                ss.sortkinds.ARRAY,
                self._convert_sort(sort.index_type),
                self._convert_sort(sort.elem_type),
            )
        elif sort.is_bool_type():
            c_sort = self.make_sort(ss.sortkinds.BOOL)
        elif sort.is_bv_type():
            c_sort = self.make_sort(ss.sortkinds.BV, sort.width)
        elif sort.is_function_type():
            sig = [self._convert_sort(s) for s in sort.param_types]
            sig.append(self._convert_sort(sort.return_type))
            c_sort = self.make_sort(ss.sortkinds.FUNCTION, sig)
        elif sort.is_int_type():
            c_sort = self.make_sort(ss.sortkinds.INT)
        elif sort.is_real_type():
            c_sort = self.make_sort(ss.sortkinds.REAL)
        else:
            raise ConvertExpressionError(f'Unsupported sort: {sort}')

        return self.declared_sorts.setdefault(sort, c_sort)


    # Declarations
    @check_args(operator.eq, 0)
    def walk_symbol(self, formula, args, **kwargs):
        try:
            return self.declared_syms[formula]
        except KeyError:
            pass

        sort_i = formula.symbol_type()
        sort = self._convert_sort(sort_i)
        res = self.make_symbol(formula.symbol_name(), sort)

        if sort_i.is_function_type():
            return self.declared_funs.setdefault(formula, res)
        else:
            return self.declared_vars.setdefault(formula, res)

    @check_args(operator.eq, 0)
    def _walk_constant(self, formula, args, **kwargs):
        sort = self._convert_sort(formula.constant_type())
        if formula.constant_type().is_bool_type():
            res = self.make_term(bool(formula.constant_value()))
        elif formula.constant_type().is_real_type():
            val = formula.constant_value()
            res = self.make_term(f'{val.numerator}/{val.denominator}', sort)
        else:
            res = self.make_term(repr(formula.constant_value()), sort)
        return res

    walk_bool_constant = _walk_constant
    walk_bv_constant = _walk_constant
    walk_int_constant = _walk_constant
    walk_real_constant = _walk_constant

    # Bool operators
    walk_and = make_walk_variadic(2, ss.primops.And)
    walk_or = make_walk_variadic(2, ss.primops.Or)
    walk_not = make_walk_unary(ss.primops.Not)
    walk_iff = make_walk_variadic(2, ss.primops.Equal)
    walk_implies = make_walk_binary(ss.primops.Implies)

    # Polymorphic Operators
    walk_ite = make_walk_nary(3, ss.primops.Ite)

    def walk_function(self, formula, args, **kwargs):
        name = formula.function_name()
        f = self.walk_symbol(name, name.args())
        res = self.make_term(ss.primops.Apply, [f, *args])
        return res

    # Int / real operatos
    walk_lt = make_walk_binary(ss.primops.Lt)
    walk_le = make_walk_binary(ss.primops.Le)
    walk_equals = make_walk_binary(ss.primops.Equal)
    walk_ge = make_walk_binary(ss.primops.Ge)
    walk_gt = make_walk_binary(ss.primops.Gt)

    walk_plus = make_walk_variadic(2, ss.primops.Plus)
    walk_times = make_walk_variadic(2, ss.primops.Mult)

    walk_minus = make_walk_binary(ss.primops.Minus)
    walk_div = make_walk_binary(ss.primops.Div)
    walk_pow = make_walk_binary(ss.primops.Pow)

    walk_toreal = make_walk_unary(ss.primops.To_Real)

    # BV Operators
    walk_bv_add = make_walk_binary(ss.primops.BVAdd)
    walk_bv_and = make_walk_binary(ss.primops.BVAnd)
    walk_bv_ashr = make_walk_binary(ss.primops.BVAshr)
    walk_bv_comp = make_walk_binary(ss.primops.BVComp)
    walk_bv_concat = make_walk_binary(ss.primops.Concat)

    @check_args(operator.eq, 1)
    def walk_bv_extract(self, formula, args, **kwargs):
        res = self.make_term(
            ss.Op(
                ss.primops.Extract,
                formula.bv_extract_end(),
                formula.bv_extract_start(),
            ),
            *args
        )
        return res

    walk_bv_lshl = make_walk_binary(ss.primops.BVShl)
    walk_bv_lshr = make_walk_binary(ss.primops.BVLshr)
    walk_bv_mul = make_walk_binary(ss.primops.BVMul)
    walk_bv_neg = make_walk_unary(ss.primops.BVNeg)
    walk_bv_not = make_walk_unary(ss.primops.BVNot)
    walk_bv_or = make_walk_binary(ss.primops.BVOr)

    @check_args(operator.eq, 1)
    def walk_bv_rol(self, formula, args, **kwargs):
        res = self.make_term(
            ss.Op(ss.primops.Rotate_Left, formula.bv_rotation_step()),
            *args
        )
        return res

    @check_args(operator.eq, 1)
    def walk_bv_ror(self, formula, args, **kwargs):
        res = self.make_term(
            ss.Op(ss.primops.Rotate_Right, formula.bv_rotation_step()),
            *args
        )
        return res

    walk_bv_sdiv = make_walk_binary(ss.primops.BVSdiv)

    @check_args(operator.eq, 1)
    def walk_bv_sext(self, formula, args, **kwargs):
        res = self.make_term(
            ss.Op(ss.primops.Sign_Extend, formula.bv_extend_step()),
            *args
        )
        return res

    walk_bv_sle = make_walk_binary(ss.primops.BVSle)
    walk_bv_slt = make_walk_binary(ss.primops.BVSlt)
    walk_bv_srem = make_walk_binary(ss.primops.BVSrem)
    walk_bv_sub = make_walk_binary(ss.primops.BVSub)
    walk_bv_tonatural = make_walk_unary(ss.primops.BV_To_Nat)
    walk_bv_udiv = make_walk_binary(ss.primops.BVUdiv)
    walk_bv_ule = make_walk_binary(ss.primops.BVUle)
    walk_bv_ult = make_walk_binary(ss.primops.BVUlt)
    walk_bv_urem = make_walk_binary(ss.primops.BVUrem)
    walk_bv_xor = make_walk_binary(ss.primops.BVXor)

    @check_args(operator.eq, 1)
    def walk_bv_zext(self, formula, args, **kwargs):
        res = self.make_term(
            ss.Op(ss.primops.Zero_Extend, formula.bv_extend_step()),
            *args
        )
        return res

    #array operators
    walk_array_select = make_walk_binary(ss.primops.Select)
    walk_array_store = make_walk_nary(3, ss.primops.Store)


_INDEXED_OPERATORS = frozenset((
    ss.primops.Extract,
    ss.primops.Repeat,
    ss.primops.Rotate_Left,
    ss.primops.Rotate_Right,
    ss.primops.Sign_Extend,
    ss.primops.Zero_Extend,
))


class BackVisitor(ss.TermDagVisitor):
    def __init__(self, mgr):
        self.mgr = mgr
        self.convertion_table = {
            ss.primops.Abs: self._convert_abs,
            ss.primops.And: mgr.And,
            ss.primops.Apply: self._convert_apply,
            ss.primops.BVAdd: mgr.BVAdd,
            ss.primops.BVAnd: mgr.BVAnd,
            ss.primops.BVAshr: mgr.BVAShr,
            ss.primops.BVComp: mgr.BVComp,
            ss.primops.BVLshr: mgr.BVLShr,
            ss.primops.BVMul: mgr.BVMul,
            ss.primops.BVNand: mgr.BVNand,
            ss.primops.BVNeg: mgr.BVNeg,
            ss.primops.BVNor: mgr.BVNor,
            ss.primops.BVNot: mgr.BVNot,
            ss.primops.BVOr: mgr.BVOr,
            ss.primops.BVSdiv: mgr.BVSDiv,
            ss.primops.BVSge: mgr.BVSGE,
            ss.primops.BVSgt: mgr.BVSGT,
            ss.primops.BVShl: mgr.BVLShl,
            ss.primops.BVSle: mgr.BVSLE,
            ss.primops.BVSlt: mgr.BVSLT,
            ss.primops.BVSmod: mgr.BVSMod,
            ss.primops.BVSrem: mgr.BVSRem,
            ss.primops.BVSub: mgr.BVSub,
            ss.primops.BVUdiv: mgr.BVUDiv,
            ss.primops.BVUge: mgr.BVUGE,
            ss.primops.BVUgt: mgr.BVUGT,
            ss.primops.BVUle: mgr.BVULE,
            ss.primops.BVUlt: mgr.BVULT,
            ss.primops.BVUrem: mgr.BVURem,
            ss.primops.BVXnor: mgr.BVXnor,
            ss.primops.BVXor: mgr.BVXor,
            ss.primops.BV_To_Nat: mgr.BVToNatural,
            ss.primops.Concat: mgr.BVConcat,
            ss.primops.Distinct: mgr.AllDifferent,
            ss.primops.Div: mgr.Div,
            ss.primops.Equal: mgr.EqualsOrIff,
            #ss.primops.Exists:
            ss.primops.Extract: self._convert_extract,
            #ss.primops.Forall:
            ss.primops.Ge: mgr.GE,
            ss.primops.Gt: mgr.GT,
            ss.primops.Implies: mgr.Implies,
            #ss.primops.Int_To_BV: NOT SUPPORTED BY PYSMT
            #ss.primops.Is_Int: NOT SUPPORTED BY PYSMT
            ss.primops.Ite: mgr.Ite,
            ss.primops.Le: mgr.LE,
            ss.primops.Lt: mgr.LT,
            ss.primops.Minus: mgr.Minus,
            #ss.primops.Mod: NOT SUPPORTED BY PYSMT
            ss.primops.Mult: mgr.Times,
            ss.primops.Negate: self._convert_negate,
            ss.primops.Not: mgr.Not,
            ss.primops.Or: mgr.Or,
            ss.primops.Plus: mgr.Plus,
            ss.primops.Pow: mgr.Pow,
            ss.primops.Repeat: mgr.BVRepeat,
            ss.primops.Rotate_Left: mgr.BVRol,
            ss.primops.Rotate_Right: mgr.BVRor,
            ss.primops.Select: mgr.Select,
            ss.primops.Sign_Extend: mgr.BVSExt,
            ss.primops.Store: mgr.Store,
            #ss.primops.To_Int: NOT SUPPORTED BY PYSMT
            ss.primops.To_Real: mgr.ToReal,
            ss.primops.Xor: mgr.Xor,
            ss.primops.Zero_Extend: mgr.BVZExt,
        }

    def visit_term(self, term, new_children):
        op = term.get_op()
        if op:
            indices = []
            if op.num_idx:
                assert op.primop in _INDEXED_OPERATORS
                indices = [op.idx0]
                if op.num_idx == 2:
                    indices.append(op.idx1)
                else:
                    assert op.num_idx == 1
            primop = op.primop
            if primop not in self.convertion_table:
                raise NotImplementedError()
            return self.convertion_table[primop](*new_children, *indices)
        elif new_children:
            assert term.get_sort().get_sort_kind() is ss.sortkinds.ARRAY
            Kt = self._convert_sort(term.get_sort().get_indexsort())
            return self.mgr.Array(Kt, *new_children, {})
        elif term.is_value():
            return self._convert_value(term)
        elif term.is_symbolic_const():
            sort = self._convert_sort(term.get_sort())
            return self.mgr.Symbol(str(term), sort)
        else:
            assert term.get_sort().get_sort_kind() is ss.sortkinds.FUNCTION
            sort = self._convert_sort(term.get_sort())
            return slf.mgr.Symbol(str(term), sort)

    def _convert_sort(self, sort):
        kind = sort.get_sort_kind()
        if kind is ss.sortkinds.ARRAY:
            Kt = self._convert_sort(sort.get_indexsort())
            Vt = self._convert_sort(sort.get_elemsort())
            return pysmt_types.ArrayType(Kt, Vt)
        elif kind is ss.sortkinds.BOOL:
            return pysmt_types.BOOL
        elif kind is ss.sortkinds.BV:
            return pysmt_types.BVType(sort.get_width())
        elif kind is ss.sortkinds.FUNCTION:
            domain = [self._convert_sort(s) for s in sort.get_domain_sorts()]
            codomain = self._convert_sort(sort.get_codomain())
            return pysmt_types.FunctionType(codomain, domain)
        elif kind is ss.sortkinds.INT:
            return pysmt_types.INT
        else:
            assert kind is ss.sortkinds.REAL
            return pysmt_types.REAL

    def _convert_value(self, term, sort=None):
        # because smt-switch backends cannot be trusted to maintain
        # sorts we must allow the sort to be manually passed
        if sort is None:
            sort = self._convert_sort(term.get_sort())

        if sort.is_array_type():
            args = self._convert_array_value(term, sort)
            return self.mgr.Array(*args)
        elif sort.is_bool_type():
            return self.mgr.Bool(bool(term))
        elif sort.is_bv_type():
            return self.mgr.BV(int(term), sort.width)
        elif sort.is_function_type():
            raise NotImplementedError()
        elif sort.is_int_type():
            return self.mgr.Int(int(term))
        elif sort.is_real_type():
            r = _parse_real(term)
            return self.mgr.Real(r)
        else:
            raise ConvertExpressionError(f'Unsupported sort: {sort}')

    def _convert_array_value(self, arr, sort):
        assignment = {}
        while arr.get_op():
            arr, idx, elem = [x for x in arr]
            idx = self._convert_value(idx, sort.index_type)
            val = self._convert_value(elem, sort.elem_type)
            assignment[idx] = val

        children = [x for x in arr]
        if not children:
            default = self._make_0(sort.elem_type)
        else:
            assert len(children) == 1
            default = self._convert_value(children[0], sort.elem_type)
        return sort.index_type, default, assignment

    def _make_0(self, sort):
        if sort.is_array_type():
            return self.mgr.Array(sort.index_type, self._make_0(sort.elem_type))
        if sort.is_bool_type():
            return self.mgr.Bool(0)
        elif sort.is_bv_type():
            return self.mgr.BV(0, sort.width)
        elif sort.is_int_type():
            return self.mgr.Int(0)
        elif sort.is_real_type():
            return self.mgr.Real(0)
        else:
            raise TypeError(f'Unsupported sort: {sort}')

    def _convert_abs(self, child):
        assert child.get_type().is_int_type()
        z = self.mgr.Int(0)
        return self.mgr.Ite(self.mgr.GE(child, z), child, self.mgr.Minus(z, child))

    def _convert_apply(self, name, *args):
        return self.mgr.Function(name, args)

    def _convert_negate(self, child):
        T = child.get_type()
        assert T.is_int_type() or T.is_real_type()
        if T.is_int_type():
            z = self.mgr.Int(0)
        else:
            z = self.mgr.Real(0)
        return self.mgr.Minus(z, child)

    def _convert_extract(self, child, end, start):
        return self.mgr.BVExtract(child, start, end)
