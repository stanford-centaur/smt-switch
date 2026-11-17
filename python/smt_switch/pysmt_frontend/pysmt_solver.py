# SPDX-FileCopyrightText: 2021 the smt-switch authors
# SPDX-FileContributor: Caleb Donovick
# SPDX-License-Identifier: BSD-3-Clause

import functools as ft
import gc
import itertools as it
import operator
from collections import ChainMap

from pysmt import typing as pysmt_types
from pysmt.decorators import catch_conversion_error, clear_pending_pop
from pysmt.exceptions import (
    ConvertExpressionError,
    PysmtValueError,
    SolverReturnedUnknownResultError,
    UndefinedLogicError,
)
from pysmt.logics import SMTLIB2_LOGICS, get_logic
from pysmt.solvers.eager import EagerModel
from pysmt.solvers.smtlib import SmtLibBasicSolver, SmtLibIgnoreMixin
from pysmt.solvers.solver import (
    Converter,
    IncrementalTrackingSolver,
    SolverOptions,
)
from pysmt.walkers import DagWalker

import smt_switch as ss
from smt_switch.api import _parse_number

SWITCH_SOLVERS = {}


class SwitchOptions(SolverOptions):
    def __call__(self, solver):
        if self.generate_models:
            solver.solver.set_opt("produce-models", "true")
        if self.incremental:
            solver.solver.set_opt("incremental", "true")

        try:
            for k, v in self.solver_options.items():
                solver.solver.set_opt(k, v)
        except RuntimeError as err:
            raise PysmtValueError(f"Error setting the option '{k}={v}'") from err


class _SwitchSolver(IncrementalTrackingSolver, SmtLibBasicSolver, SmtLibIgnoreMixin):
    OptionsClass = SwitchOptions

    def __init__(self, environment, logic, **options):
        IncrementalTrackingSolver.__init__(
            self, environment=environment, logic=logic, **options
        )

        self.solver = self._create_solver()
        self.options(self)
        self.mgr = environment.formula_manager
        self.converter = SwitchConverter(environment, self.solver, self.mgr)

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
        # HACK because smt-switch sometimes loses sorts  # noqa: FIX004
        # we can't use back
        # should be: `r_val = self.converter.back(val)`
        # hence the private call below
        r_val = self.converter.back_walker._convert_value(val, sort)  # noqa: SLF001
        if r_val.get_type() != sort:
            raise ConvertExpressionError(
                f"Converting the value of {item} produced sort "
                f"{r_val.get_type()} rather than {sort}"
            )
        return r_val

    @clear_pending_pop
    def _reset_assertions(self):
        self.solver.reset_assertions()

    # `named` goes unused: this backend does not support named assertions.
    # pysmt's IncrementalTrackingSolver passes it by keyword, so the parameter
    # cannot be renamed to `_named` to mark it unused the way the walker
    # callbacks below are.
    @clear_pending_pop
    def _add_assertion(self, formula, named=None):  # noqa: ARG002
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
        if res.is_unsat():
            return False
        raise SolverReturnedUnknownResultError

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


if "btor" in ss.solvers:
    logics_params = {
        "quantifier_free": [True],
        "arrays": [True, False],
        "bit_vectors": [True, False],
        "uninterpreted": [True, False],
    }

    class SwitchBtor(_SwitchSolver):
        LOGICS = _build_logics(logics_params)
        _create_solver = staticmethod(ft.partial(ss.create_btor_solver, logging=False))

        @clear_pending_pop
        def _reset_assertions(self):
            self.solver = self._create_solver()
            self.converter = SwitchConverter(self.environment, self.solver, self.mgr)
            self.options(self)

    SWITCH_SOLVERS["btor"] = SwitchBtor


if "bitwuzla" in ss.solvers:
    logics_params = {
        "quantifier_free": [True],
        "arrays": [True, False],
        "bit_vectors": [True],
        "uninterpreted": [True, False],
        "floating_point": [True, False],
    }

    class SwitchBitwuzla(_SwitchSolver):
        LOGICS = _build_logics(logics_params)
        _create_solver = staticmethod(
            ft.partial(ss.create_bitwuzla_solver, logging=False)
        )

    SWITCH_SOLVERS["bitwuzla"] = SwitchBitwuzla


if "msat" in ss.solvers:
    logics_params = {
        "quantifier_free": [True],
        "arrays": [True, False],
        "bit_vectors": [True, False],
        "uninterpreted": [True, False],
        "integer_arithmetic": [True, False],
        "integer_difference": [True, False],
        "real_arithmetic": [True, False],
        "real_difference": [True, False],
        "linear": [True],
    }

    class SwitchMsat(_SwitchSolver):
        LOGICS = _build_logics(logics_params)
        _create_solver = staticmethod(ft.partial(ss.create_msat_solver, logging=False))

    SWITCH_SOLVERS["msat"] = SwitchMsat

if "cvc5" in ss.solvers:
    logics_params = {
        "quantifier_free": [True],
        "arrays": [True, False],
        "bit_vectors": [True, False],
        "uninterpreted": [True, False],
        "integer_arithmetic": [True, False],
        "integer_difference": [True, False],
        "real_arithmetic": [True, False],
        "real_difference": [True, False],
        "linear": [True],
    }

    class SwitchCvc5(_SwitchSolver):
        LOGICS = _build_logics(logics_params)
        _create_solver = staticmethod(ft.partial(ss.create_cvc5_solver, logging=False))

        def _exit(self):
            super()._exit()
            # ensure prompt collection of the solver object
            # to avoid heisenbug
            gc.collect()

    SWITCH_SOLVERS["cvc5"] = SwitchCvc5


def check_args(cmp, n):
    def wrapper(f):
        @ft.wraps(f)
        def walk_op(self, formula, args, **kwargs):
            if not cmp(len(args), n):
                raise ConvertExpressionError("Incorrect number of arguments")
            return f(self, formula, args, **kwargs)

        return walk_op

    return wrapper


def make_walk_nary(n, kind):
    @check_args(operator.eq, n)
    def walk_op(self, _formula, args, **_kwargs):
        return self.make_term(kind, *args)

    return walk_op


make_walk_unary = ft.partial(make_walk_nary, 1)
make_walk_binary = ft.partial(make_walk_nary, 2)


def make_walk_variadic(n, kind):
    @check_args(operator.ge, n)
    def walk_op(self, _formula, args, **_kwargs):
        builder = ft.partial(self.make_term, kind)
        return ft.reduce(builder, args)

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
            raise ConvertExpressionError(f"Unsupported sort: {sort}")

        return self.declared_sorts.setdefault(sort, c_sort)

    # Declarations
    @check_args(operator.eq, 0)
    def walk_symbol(self, formula, _args, **_kwargs):
        try:
            return self.declared_syms[formula]
        except KeyError:
            pass

        sort_i = formula.symbol_type()
        sort = self._convert_sort(sort_i)
        res = self.make_symbol(formula.symbol_name(), sort)

        if sort_i.is_function_type():
            return self.declared_funs.setdefault(formula, res)
        return self.declared_vars.setdefault(formula, res)

    @check_args(operator.eq, 0)
    def _walk_constant(self, formula, _args, **_kwargs):
        sort = self._convert_sort(formula.constant_type())
        if formula.constant_type().is_bool_type():
            res = self.make_term(bool(formula.constant_value()))
        elif formula.constant_type().is_real_type():
            val = formula.constant_value()
            res = self.make_term(f"{val.numerator}/{val.denominator}", sort)
        else:
            res = self.make_term(str(formula.constant_value()), sort)
        return res

    walk_bool_constant = _walk_constant
    walk_bv_constant = _walk_constant
    walk_int_constant = _walk_constant
    walk_real_constant = _walk_constant

    # Bool operators
    walk_and = make_walk_variadic(2, ss.opkinds.And)
    walk_or = make_walk_variadic(2, ss.opkinds.Or)
    walk_not = make_walk_unary(ss.opkinds.Not)
    walk_iff = make_walk_variadic(2, ss.opkinds.Equal)
    walk_implies = make_walk_binary(ss.opkinds.Implies)

    # Polymorphic Operators
    walk_ite = make_walk_nary(3, ss.opkinds.Ite)

    def walk_function(self, formula, args, **_kwargs):
        name = formula.function_name()
        f = self.walk_symbol(name, name.args())
        return self.make_term(ss.opkinds.Apply, [f, *args])

    # Int / real operators
    walk_lt = make_walk_binary(ss.opkinds.Lt)
    walk_le = make_walk_binary(ss.opkinds.Le)
    walk_equals = make_walk_binary(ss.opkinds.Equal)
    walk_ge = make_walk_binary(ss.opkinds.Ge)
    walk_gt = make_walk_binary(ss.opkinds.Gt)

    walk_plus = make_walk_variadic(2, ss.opkinds.Plus)
    walk_times = make_walk_variadic(2, ss.opkinds.Mult)

    walk_minus = make_walk_binary(ss.opkinds.Minus)
    walk_div = make_walk_binary(ss.opkinds.Div)
    walk_pow = make_walk_binary(ss.opkinds.Pow)

    walk_toreal = make_walk_unary(ss.opkinds.To_Real)

    # BV Operators
    walk_bv_add = make_walk_binary(ss.opkinds.BVAdd)
    walk_bv_and = make_walk_binary(ss.opkinds.BVAnd)
    walk_bv_ashr = make_walk_binary(ss.opkinds.BVAshr)
    walk_bv_comp = make_walk_binary(ss.opkinds.BVComp)
    walk_bv_concat = make_walk_binary(ss.opkinds.Concat)

    @check_args(operator.eq, 1)
    def walk_bv_extract(self, formula, args, **_kwargs):
        return self.make_term(
            ss.Op(
                ss.opkinds.Extract,
                formula.bv_extract_end(),
                formula.bv_extract_start(),
            ),
            *args,
        )

    walk_bv_lshl = make_walk_binary(ss.opkinds.BVShl)
    walk_bv_lshr = make_walk_binary(ss.opkinds.BVLshr)
    walk_bv_mul = make_walk_binary(ss.opkinds.BVMul)
    walk_bv_neg = make_walk_unary(ss.opkinds.BVNeg)
    walk_bv_not = make_walk_unary(ss.opkinds.BVNot)
    walk_bv_or = make_walk_binary(ss.opkinds.BVOr)

    @check_args(operator.eq, 1)
    def walk_bv_rol(self, formula, args, **_kwargs):
        return self.make_term(
            ss.Op(ss.opkinds.Rotate_Left, formula.bv_rotation_step()), *args
        )

    @check_args(operator.eq, 1)
    def walk_bv_ror(self, formula, args, **_kwargs):
        return self.make_term(
            ss.Op(ss.opkinds.Rotate_Right, formula.bv_rotation_step()), *args
        )

    walk_bv_sdiv = make_walk_binary(ss.opkinds.BVSdiv)

    @check_args(operator.eq, 1)
    def walk_bv_sext(self, formula, args, **_kwargs):
        return self.make_term(
            ss.Op(ss.opkinds.Sign_Extend, formula.bv_extend_step()), *args
        )

    walk_bv_sle = make_walk_binary(ss.opkinds.BVSle)
    walk_bv_slt = make_walk_binary(ss.opkinds.BVSlt)
    walk_bv_srem = make_walk_binary(ss.opkinds.BVSrem)
    walk_bv_sub = make_walk_binary(ss.opkinds.BVSub)
    walk_bv_tonatural = make_walk_unary(ss.opkinds.BV_To_Nat)
    walk_ubv_to_int = make_walk_unary(ss.opkinds.UBV_To_Int)
    walk_sbv_to_int = make_walk_unary(ss.opkinds.SBV_To_Int)
    walk_bv_udiv = make_walk_binary(ss.opkinds.BVUdiv)
    walk_bv_ule = make_walk_binary(ss.opkinds.BVUle)
    walk_bv_ult = make_walk_binary(ss.opkinds.BVUlt)
    walk_bv_urem = make_walk_binary(ss.opkinds.BVUrem)
    walk_bv_xor = make_walk_binary(ss.opkinds.BVXor)

    @check_args(operator.eq, 1)
    def walk_bv_zext(self, formula, args, **_kwargs):
        return self.make_term(
            ss.Op(ss.opkinds.Zero_Extend, formula.bv_extend_step()), *args
        )

    # array operators
    walk_array_select = make_walk_binary(ss.opkinds.Select)
    walk_array_store = make_walk_nary(3, ss.opkinds.Store)


class BackVisitor(ss.TermDagVisitor):
    def __init__(self, mgr):
        self.mgr = mgr
        self.convertion_table = {
            ss.opkinds.Abs: self._convert_abs,
            ss.opkinds.And: mgr.And,
            ss.opkinds.Apply: self._convert_apply,
            ss.opkinds.BVAdd: mgr.BVAdd,
            ss.opkinds.BVAnd: mgr.BVAnd,
            ss.opkinds.BVAshr: mgr.BVAShr,
            ss.opkinds.BVComp: mgr.BVComp,
            ss.opkinds.BVLshr: mgr.BVLShr,
            ss.opkinds.BVMul: mgr.BVMul,
            ss.opkinds.BVNand: mgr.BVNand,
            ss.opkinds.BVNeg: mgr.BVNeg,
            ss.opkinds.BVNor: mgr.BVNor,
            ss.opkinds.BVNot: mgr.BVNot,
            ss.opkinds.BVOr: mgr.BVOr,
            ss.opkinds.BVSdiv: mgr.BVSDiv,
            ss.opkinds.BVSge: mgr.BVSGE,
            ss.opkinds.BVSgt: mgr.BVSGT,
            ss.opkinds.BVShl: mgr.BVLShl,
            ss.opkinds.BVSle: mgr.BVSLE,
            ss.opkinds.BVSlt: mgr.BVSLT,
            ss.opkinds.BVSmod: mgr.BVSMod,
            ss.opkinds.BVSrem: mgr.BVSRem,
            ss.opkinds.BVSub: mgr.BVSub,
            ss.opkinds.BVUdiv: mgr.BVUDiv,
            ss.opkinds.BVUge: mgr.BVUGE,
            ss.opkinds.BVUgt: mgr.BVUGT,
            ss.opkinds.BVUle: mgr.BVULE,
            ss.opkinds.BVUlt: mgr.BVULT,
            ss.opkinds.BVUrem: mgr.BVURem,
            ss.opkinds.BVXnor: mgr.BVXnor,
            ss.opkinds.BVXor: mgr.BVXor,
            ss.opkinds.BV_To_Nat: mgr.BVToNatural,
            ss.opkinds.UBV_To_Int: mgr.BVToNatural,
            # ss.opkinds.SBV_To_Int: NOT SUPPORTED BY PYSMT
            ss.opkinds.Concat: mgr.BVConcat,
            ss.opkinds.Distinct: mgr.AllDifferent,
            ss.opkinds.Div: mgr.Div,
            ss.opkinds.Equal: mgr.EqualsOrIff,
            # ss.opkinds.Exists:
            ss.opkinds.Extract: self._convert_extract,
            # ss.opkinds.Forall:
            ss.opkinds.Ge: mgr.GE,
            ss.opkinds.Gt: mgr.GT,
            ss.opkinds.Implies: mgr.Implies,
            # ss.opkinds.Int_To_BV: NOT SUPPORTED BY PYSMT
            # ss.opkinds.Is_Int: NOT SUPPORTED BY PYSMT
            ss.opkinds.Ite: mgr.Ite,
            ss.opkinds.Le: mgr.LE,
            ss.opkinds.Lt: mgr.LT,
            ss.opkinds.Minus: mgr.Minus,
            # ss.opkinds.Mod: NOT SUPPORTED BY PYSMT
            ss.opkinds.Mult: mgr.Times,
            ss.opkinds.Negate: self._convert_negate,
            ss.opkinds.Not: mgr.Not,
            ss.opkinds.Or: mgr.Or,
            ss.opkinds.Plus: mgr.Plus,
            ss.opkinds.Pow: mgr.Pow,
            ss.opkinds.Repeat: mgr.BVRepeat,
            ss.opkinds.Rotate_Left: mgr.BVRol,
            ss.opkinds.Rotate_Right: mgr.BVRor,
            ss.opkinds.Select: mgr.Select,
            ss.opkinds.Sign_Extend: mgr.BVSExt,
            ss.opkinds.Store: mgr.Store,
            # ss.opkinds.To_Int: NOT SUPPORTED BY PYSMT
            ss.opkinds.To_Real: mgr.ToReal,
            ss.opkinds.Xor: mgr.Xor,
            ss.opkinds.Zero_Extend: mgr.BVZExt,
        }

    def visit_term(self, term, new_children):
        op = term.get_op()
        if op:
            indices = []
            if op.num_idx:
                indices = [op.idx0]
                if op.num_idx > 1:
                    indices.append(op.idx1)
            kind = op.kind
            if kind not in self.convertion_table:
                raise NotImplementedError(f"Unsupported operator: {kind}")
            return self.convertion_table[kind](*new_children, *indices)

        sort = term.get_sort()
        if new_children:
            if sort.get_kind() is not ss.sortkinds.ARRAY:
                raise ConvertExpressionError(
                    f"Only an array term can have children without an operator: {term}"
                )
            index_type = self._convert_sort(sort.get_indexsort())
            return self.mgr.Array(index_type, *new_children, {})
        if term.is_value():
            return self._convert_value(term)
        # A symbolic constant, or an uninterpreted function symbol.
        if term.is_symbolic_const() or sort.get_kind() is ss.sortkinds.FUNCTION:
            return self.mgr.Symbol(term.get_symbol_name(), self._convert_sort(sort))
        raise ConvertExpressionError(f"Cannot convert term: {term}")

    def _convert_sort(self, sort):
        kind = sort.get_kind()
        if kind is ss.sortkinds.ARRAY:
            index_type = self._convert_sort(sort.get_indexsort())
            elem_type = self._convert_sort(sort.get_elemsort())
            return pysmt_types.ArrayType(index_type, elem_type)
        if kind is ss.sortkinds.BOOL:
            return pysmt_types.BOOL
        if kind is ss.sortkinds.BV:
            return pysmt_types.BVType(sort.get_width())
        if kind is ss.sortkinds.FUNCTION:
            domain = [self._convert_sort(s) for s in sort.get_domain_sorts()]
            codomain = self._convert_sort(sort.get_codomain())
            return pysmt_types.FunctionType(codomain, domain)
        if kind is ss.sortkinds.INT:
            return pysmt_types.INT
        if kind is ss.sortkinds.REAL:
            return pysmt_types.REAL
        raise ConvertExpressionError(f"Unsupported sort: {sort}")

    def _convert_value(self, term, sort=None):
        # because smt-switch backends cannot be trusted to maintain
        # sorts we must allow the sort to be manually passed
        if sort is None:
            sort = self._convert_sort(term.get_sort())

        if sort.is_array_type():
            args = self._convert_array_value(term, sort)
            return self.mgr.Array(*args)
        if sort.is_bool_type():
            return self.mgr.Bool(bool(term))
        if sort.is_bv_type():
            return self.mgr.BV(int(term), sort.width)
        if sort.is_function_type():
            raise NotImplementedError
        if sort.is_int_type():
            return self.mgr.Int(int(term))
        if sort.is_real_type():
            return self.mgr.Real(_parse_number(str(term)))
        raise ConvertExpressionError(f"Unsupported sort: {sort}")

    def _convert_array_value(self, arr, sort):
        assignment = {}
        while arr.get_op():
            arr, idx, elem = list(arr)
            idx = self._convert_value(idx, sort.index_type)
            val = self._convert_value(elem, sort.elem_type)
            assignment[idx] = val

        children = list(arr)
        if not children:
            default = self._make_0(sort.elem_type)
        elif len(children) == 1:
            default = self._convert_value(children[0], sort.elem_type)
        else:
            raise ConvertExpressionError(
                f"An array default takes one child, got {len(children)}"
            )
        return sort.index_type, default, assignment

    def _make_0(self, sort):
        if sort.is_array_type():
            return self.mgr.Array(sort.index_type, self._make_0(sort.elem_type))
        if sort.is_bool_type():
            return self.mgr.Bool(0)
        if sort.is_bv_type():
            return self.mgr.BV(0, sort.width)
        if sort.is_int_type():
            return self.mgr.Int(0)
        if sort.is_real_type():
            return self.mgr.Real(0)
        raise TypeError(f"Unsupported sort: {sort}")

    def _convert_abs(self, child):
        child_type = child.get_type()
        if not child_type.is_int_type():
            raise ConvertExpressionError(
                f"Cannot take the absolute value of a term of type {child_type}"
            )
        z = self.mgr.Int(0)
        return self.mgr.Ite(self.mgr.GE(child, z), child, self.mgr.Minus(z, child))

    def _convert_apply(self, name, *args):
        return self.mgr.Function(name, args)

    def _convert_negate(self, child):
        child_type = child.get_type()
        if not (child_type.is_int_type() or child_type.is_real_type()):
            raise ConvertExpressionError(f"Cannot negate a term of type {child_type}")
        z = self.mgr.Int(0) if child_type.is_int_type() else self.mgr.Real(0)
        return self.mgr.Minus(z, child)

    def _convert_extract(self, child, end, start):
        return self.mgr.BVExtract(child, start, end)
