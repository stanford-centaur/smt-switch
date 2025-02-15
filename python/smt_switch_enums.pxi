import sys
from types import ModuleType

from smt_switch_enums cimport (
    c_PrimOp,
    c_ResultType,
    c_SolverAttribute,
    c_SolverEnum,
    c_SortKind,
    to_string
)

from smt_switch_enums cimport (
    # SortKind
    c_ARRAY,
    c_BOOL,
    c_BV,
    c_INT,
    c_REAL,
    c_FUNCTION,
    # SolverEnum
    c_BTOR,
    c_CVC5,
    c_MSAT,
    c_YICES2,
    c_MSAT_INTERPOLATOR,
    c_CVC5_INTERPOLATOR,
    c_GENERIC_SOLVER,
    # SolverAttribute
    c_TERMITER,
    c_THEORY_INT,
    c_THEORY_REAL,
    c_ARRAY_MODELS,
    c_CONSTARR,
    c_FULL_TRANSFER,
    c_ARRAY_FUN_BOOLS,
    c_UNSAT_CORE,
    c_THEORY_DATATYPE,
    c_QUANTIFIERS,
    c_BOOL_BV1_ALIASING,
    c_TIMELIMIT,
    # PrimOp
    c_And,
    c_Or,
    c_Xor,
    c_Not,
    c_Implies,
    c_Ite,
    c_Equal,
    c_Distinct,
    c_Apply,
    c_Plus,
    c_Minus,
    c_Negate,
    c_Mult,
    c_Div,
    c_Lt,
    c_Le,
    c_Gt,
    c_Ge,
    # Integers only
    c_Mod,
    c_Abs,
    c_Pow,
    # Int/Real Conversion and Queries
    c_To_Real,
    c_To_Int,
    c_Is_Int,
    # Fixed Size BitVector Theory
    c_Concat,
    c_Extract,
    c_BVNot,
    c_BVNeg,
    c_BVAnd,
    c_BVOr,
    c_BVXor,
    c_BVNand,
    c_BVNor,
    c_BVXnor,
    c_BVComp,
    c_BVAdd,
    c_BVSub,
    c_BVMul,
    c_BVUdiv,
    c_BVSdiv,
    c_BVUrem,
    c_BVSrem,
    c_BVSmod,
    c_BVShl,
    c_BVAshr,
    c_BVLshr,
    c_BVUlt,
    c_BVUle,
    c_BVUgt,
    c_BVUge,
    c_BVSlt,
    c_BVSle,
    c_BVSgt,
    c_BVSge,
    c_Zero_Extend,
    c_Sign_Extend,
    c_Repeat,
    c_Rotate_Left,
    c_Rotate_Right,
    # BitVector Conversion
    c_BV_To_Nat,
    c_Int_To_BV,
    # Array Theory
    c_Select,
    c_Store,
    # Quantifiers
    c_Forall,
    c_Exists,
    # ResultType
    SAT,
    UNSAT,
    UNKNOWN
)

FILENAME="smt_switch_enums.pxi"
_PACKAGE_ROOT=__name__.split('.')[0]

def _add_module(m):
    sys.modules['.'.join((_PACKAGE_ROOT, m.__name__))] = m


################################################ SortKind #################################################
cdef class SortKind:
    cdef c_SortKind sk

    def __cinit__(self):
        pass

    def __eq__(self, SortKind other):
        return (<int> self.sk) == (<int> other.sk)

    def __ne__(self, SortKind other):
        return (<int> self.sk) != (<int> other.sk)

    def __hash__(self):
        return hash(<int> self.sk)

    def __str__(self):
        return to_string(self.sk).decode()

    def __repr__(self):
        return to_string(self.sk).decode()

    def as_int(self):
        return <int> self.sk


# create a sortkinds submodule
sortkinds = ModuleType('sortkinds')
# fake a submodule for dotted imports, e.g. from smt_switch.prim_ops import And
_add_module(sortkinds)
sortkinds.__file__ = FILENAME

cdef SortKind ARRAY = SortKind()
ARRAY.sk = c_ARRAY
setattr(sortkinds, 'ARRAY', ARRAY)

cdef SortKind BOOL = SortKind()
BOOL.sk = c_BOOL
setattr(sortkinds, 'BOOL', BOOL)

cdef SortKind BV = SortKind()
BV.sk = c_BV
setattr(sortkinds, 'BV', BV)

cdef SortKind INT = SortKind()
INT.sk = c_INT
setattr(sortkinds, 'INT', INT)

cdef SortKind REAL = SortKind()
REAL.sk = c_REAL
setattr(sortkinds, 'REAL', REAL)

cdef SortKind FUNCTION = SortKind()
FUNCTION.sk = c_FUNCTION
setattr(sortkinds, 'FUNCTION', FUNCTION)


################################################ SolverEnum #################################################
cdef class SolverEnum:
    cdef c_SolverEnum se

    def __cinit__(self):
        pass

    def __eq__(self, SolverEnum other):
        return (<int> self.se) == (<int> other.se)

    def __ne__(self, SolverEnum other):
        return (<int> self.se) != (<int> other.se)

    def __hash__(self):
        return hash((<int> self.se, self.name))

    def __str__(self):
        return to_string(self.se).decode()

    def __repr__(self):
        return to_string(self.se).decode()

    def as_int(self):
        return <int> self.se

# create a solverenums submodule
solverenums = ModuleType('solverenums')
# fake a submodule for dotted imports, e.g. from smt_switch.prim_ops import And
_add_module(solverenums)
solverenums.__file__ = FILENAME

cdef SolverEnum BTOR = SolverEnum()
BTOR.se = c_BTOR
setattr(solverenums, 'BTOR', BTOR)

cdef SolverEnum CVC5 = SolverEnum()
CVC5.se = c_CVC5
setattr(solverenums, 'CVC5', CVC5)

cdef SolverEnum MSAT = SolverEnum()
MSAT.se = c_MSAT
setattr(solverenums, 'MSAT', MSAT)

cdef SolverEnum YICES2 = SolverEnum()
YICES2.se = c_YICES2
setattr(solverenums, 'YICES2', YICES2)

cdef SolverEnum MSAT_INTERPOLATOR = SolverEnum()
MSAT_INTERPOLATOR.se = c_MSAT_INTERPOLATOR
setattr(solverenums, "MSAT_INTERPOLATOR", MSAT_INTERPOLATOR)

cdef SolverEnum CVC5_INTERPOLATOR = SolverEnum()
CVC5_INTERPOLATOR.se = c_CVC5_INTERPOLATOR
setattr(solverenums, "CVC5_INTERPOLATOR", CVC5_INTERPOLATOR)

cdef SolverEnum GENERIC_SOLVER = SolverEnum()
GENERIC_SOLVER.se = c_GENERIC_SOLVER
setattr(solverenums, "GENERIC_SOLVER", GENERIC_SOLVER)


################################################ SolverAttribute #################################################
cdef class SolverAttribute:
    cdef c_SolverAttribute sa

    def __cinit__(self):
        pass

    def __eq__(self, SolverAttribute other):
        return (<int> self.sa) == (<int> other.sa)

    def __ne__(self, SolverAttribute other):
        return (<int> self.sa) != (<int> other.sa)

    def __hash__(self):
        return hash((<int> self.sa, self.name))

    def __str__(self):
        return to_string(self.sa).decode()

    def __repr__(self):
        return to_string(self.sa).decode()

    def as_int(self):
        return <int> self.sa


# create a solverattr submodule
solverattr = ModuleType('solverattr')
# fake a submodule for dotted imports, e.g. from smt_switch.prim_ops import And
_add_module(solverattr)
solverattr.__file__ = FILENAME

cdef SolverAttribute TERMITER = SolverAttribute()
TERMITER.sa = c_TERMITER
setattr(solverattr, "TERMITER", TERMITER)

cdef SolverAttribute THEORY_INT = SolverAttribute()
THEORY_INT.sa = c_THEORY_INT
setattr(solverattr, "THEORY_INT", THEORY_INT)

cdef SolverAttribute THEORY_REAL = SolverAttribute()
THEORY_REAL.sa = c_THEORY_REAL
setattr(solverattr, "THEORY_REAL", THEORY_REAL)

cdef SolverAttribute ARRAY_MODELS = SolverAttribute()
ARRAY_MODELS.sa = c_ARRAY_MODELS
setattr(solverattr, "ARRAY_MODELS", ARRAY_MODELS)

cdef SolverAttribute CONSTARR = SolverAttribute()
CONSTARR.sa = c_CONSTARR
setattr(solverattr, "CONSTARR", CONSTARR)

cdef SolverAttribute FULL_TRANSFER = SolverAttribute()
FULL_TRANSFER.sa = c_FULL_TRANSFER
setattr(solverattr, "FULL_TRANSFER", FULL_TRANSFER)

cdef SolverAttribute ARRAY_FUN_BOOLS = SolverAttribute()
ARRAY_FUN_BOOLS.sa = c_ARRAY_FUN_BOOLS
setattr(solverattr, "ARRAY_FUN_BOOLS", ARRAY_FUN_BOOLS)

cdef SolverAttribute UNSAT_CORE = SolverAttribute()
UNSAT_CORE.sa = c_UNSAT_CORE
setattr(solverattr, "UNSAT_CORE", UNSAT_CORE)

cdef SolverAttribute THEORY_DATATYPE = SolverAttribute()
THEORY_DATATYPE.sa = c_THEORY_DATATYPE
setattr(solverattr, "THEORY_DATATYPE", THEORY_DATATYPE)

cdef SolverAttribute QUANTIFIERS = SolverAttribute()
QUANTIFIERS.sa = c_QUANTIFIERS
setattr(solverattr, "QUANTIFIERS", QUANTIFIERS)

cdef SolverAttribute BOOL_BV1_ALIASING = SolverAttribute()
BOOL_BV1_ALIASING.sa = c_BOOL_BV1_ALIASING
setattr(solverattr, "BOOL_BV1_ALIASING", BOOL_BV1_ALIASING)

cdef SolverAttribute TIMELIMIT = SolverAttribute()
TIMELIMIT.sa = c_TIMELIMIT
setattr(solverattr, "TIMELIMIT", TIMELIMIT)

################################################ PrimOps #################################################
cdef class PrimOp:
    cdef c_PrimOp po

    def __cinit__(self):
        pass

    def __eq__(self, PrimOp other):
        return (<int> self.po) == (<int> other.po)

    def __ne__(self, PrimOp other):
        return (<int> self.po) != (<int> other.po)

    def __hash__(self):
        return (<int> self.po)

    def __str__(self):
        return to_string(self.po).decode()

    def __repr__(self):
        return to_string(self.po).decode()

    def as_int(self):
        return <int> self.po

# create a primops submodule
primops = ModuleType('primops')
# fake a submodule for dotted imports, e.g. from smt_switch.prim_ops import And
_add_module(primops)
primops.__file__ = FILENAME + ".so"

cdef PrimOp And = PrimOp()
And.po = c_And
setattr(primops, 'And', And)

cdef PrimOp Or = PrimOp()
Or.po = c_Or
setattr(primops, 'Or', Or)

cdef PrimOp Xor = PrimOp()
Xor.po = c_Xor
setattr(primops, 'Xor', Xor)

cdef PrimOp Not = PrimOp()
Not.po = c_Not
setattr(primops, 'Not', Not)

cdef PrimOp Implies = PrimOp()
Implies.po = c_Implies
setattr(primops, 'Implies', Implies)

cdef PrimOp Ite = PrimOp()
Ite.po = c_Ite
setattr(primops, 'Ite', Ite)

cdef PrimOp Equal = PrimOp()
Equal.po = c_Equal
setattr(primops, 'Equal', Equal)

cdef PrimOp Distinct = PrimOp()
Distinct.po = c_Distinct
setattr(primops, 'Distinct', Distinct)

cdef PrimOp Apply = PrimOp()
Apply.po = c_Apply
setattr(primops, 'Apply', Apply)

cdef PrimOp Plus = PrimOp()
Plus.po = c_Plus
setattr(primops, 'Plus', Plus)

cdef PrimOp Minus = PrimOp()
Minus.po = c_Minus
setattr(primops, 'Minus', Minus)

cdef PrimOp Negate = PrimOp()
Negate.po = c_Negate
setattr(primops, 'Negate', Negate)

cdef PrimOp Mult = PrimOp()
Mult.po = c_Mult
setattr(primops, 'Mult', Mult)

cdef PrimOp Div = PrimOp()
Div.po = c_Div
setattr(primops, 'Div', Div)

cdef PrimOp Lt = PrimOp()
Lt.po = c_Lt
setattr(primops, 'Lt', Lt)

cdef PrimOp Le = PrimOp()
Le.po = c_Le
setattr(primops, 'Le', Le)

cdef PrimOp Gt = PrimOp()
Gt.po = c_Gt
setattr(primops, 'Gt', Gt)

cdef PrimOp Ge = PrimOp()
Ge.po = c_Ge
setattr(primops, 'Ge', Ge)

cdef PrimOp Mod = PrimOp()
Mod.po = c_Mod
setattr(primops, 'Mod', Mod)

cdef PrimOp Abs = PrimOp()
Abs.po = c_Abs
setattr(primops, 'Abs', Abs)

cdef PrimOp Pow = PrimOp()
Pow.po = c_Pow
setattr(primops, 'Pow', Pow)

cdef PrimOp To_Real = PrimOp()
To_Real.po = c_To_Real
setattr(primops, 'To_Real', To_Real)

cdef PrimOp To_Int = PrimOp()
To_Int.po = c_To_Int
setattr(primops, 'To_Int', To_Int)

cdef PrimOp Is_Int = PrimOp()
Is_Int.po = c_Is_Int
setattr(primops, 'Is_Int', Is_Int)

cdef PrimOp Concat = PrimOp()
Concat.po = c_Concat
setattr(primops, 'Concat', Concat)

cdef PrimOp Extract = PrimOp()
Extract.po = c_Extract
setattr(primops, 'Extract', Extract)

cdef PrimOp BVNot = PrimOp()
BVNot.po = c_BVNot
setattr(primops, 'BVNot', BVNot)

cdef PrimOp BVNeg = PrimOp()
BVNeg.po = c_BVNeg
setattr(primops, 'BVNeg', BVNeg)

cdef PrimOp BVAnd = PrimOp()
BVAnd.po = c_BVAnd
setattr(primops, 'BVAnd', BVAnd)

cdef PrimOp BVOr = PrimOp()
BVOr.po = c_BVOr
setattr(primops, 'BVOr', BVOr)

cdef PrimOp BVXor = PrimOp()
BVXor.po = c_BVXor
setattr(primops, 'BVXor', BVXor)

cdef PrimOp BVNand = PrimOp()
BVNand.po = c_BVNand
setattr(primops, 'BVNand', BVNand)

cdef PrimOp BVNor = PrimOp()
BVNor.po = c_BVNor
setattr(primops, 'BVNor', BVNor)

cdef PrimOp BVXnor = PrimOp()
BVXnor.po = c_BVXnor
setattr(primops, 'BVXnor', BVXnor)

cdef PrimOp BVComp = PrimOp()
BVComp.po = c_BVComp
setattr(primops, 'BVComp', BVComp)

cdef PrimOp BVAdd = PrimOp()
BVAdd.po = c_BVAdd
setattr(primops, 'BVAdd', BVAdd)

cdef PrimOp BVSub = PrimOp()
BVSub.po = c_BVSub
setattr(primops, 'BVSub', BVSub)

cdef PrimOp BVMul = PrimOp()
BVMul.po = c_BVMul
setattr(primops, 'BVMul', BVMul)

cdef PrimOp BVUdiv = PrimOp()
BVUdiv.po = c_BVUdiv
setattr(primops, 'BVUdiv', BVUdiv)

cdef PrimOp BVSdiv = PrimOp()
BVSdiv.po = c_BVSdiv
setattr(primops, 'BVSdiv', BVSdiv)

cdef PrimOp BVUrem = PrimOp()
BVUrem.po = c_BVUrem
setattr(primops, 'BVUrem', BVUrem)

cdef PrimOp BVSrem = PrimOp()
BVSrem.po = c_BVSrem
setattr(primops, 'BVSrem', BVSrem)

cdef PrimOp BVSmod = PrimOp()
BVSmod.po = c_BVSmod
setattr(primops, 'BVSmod', BVSmod)

cdef PrimOp BVShl = PrimOp()
BVShl.po = c_BVShl
setattr(primops, 'BVShl', BVShl)

cdef PrimOp BVAshr = PrimOp()
BVAshr.po = c_BVAshr
setattr(primops, 'BVAshr', BVAshr)

cdef PrimOp BVLshr = PrimOp()
BVLshr.po = c_BVLshr
setattr(primops, 'BVLshr', BVLshr)

cdef PrimOp BVUlt = PrimOp()
BVUlt.po = c_BVUlt
setattr(primops, 'BVUlt', BVUlt)

cdef PrimOp BVUle = PrimOp()
BVUle.po = c_BVUle
setattr(primops, 'BVUle', BVUle)

cdef PrimOp BVUgt = PrimOp()
BVUgt.po = c_BVUgt
setattr(primops, 'BVUgt', BVUgt)

cdef PrimOp BVUge = PrimOp()
BVUge.po = c_BVUge
setattr(primops, 'BVUge', BVUge)

cdef PrimOp BVSlt = PrimOp()
BVSlt.po = c_BVSlt
setattr(primops, 'BVSlt', BVSlt)

cdef PrimOp BVSle = PrimOp()
BVSle.po = c_BVSle
setattr(primops, 'BVSle', BVSle)

cdef PrimOp BVSgt = PrimOp()
BVSgt.po = c_BVSgt
setattr(primops, 'BVSgt', BVSgt)

cdef PrimOp BVSge = PrimOp()
BVSge.po = c_BVSge
setattr(primops, 'BVSge', BVSge)

cdef PrimOp Zero_Extend = PrimOp()
Zero_Extend.po = c_Zero_Extend
setattr(primops, 'Zero_Extend', Zero_Extend)

cdef PrimOp Sign_Extend = PrimOp()
Sign_Extend.po = c_Sign_Extend
setattr(primops, 'Sign_Extend', Sign_Extend)

cdef PrimOp Repeat = PrimOp()
Repeat.po = c_Repeat
setattr(primops, 'Repeat', Repeat)

cdef PrimOp Rotate_Left = PrimOp()
Rotate_Left.po = c_Rotate_Left
setattr(primops, 'Rotate_Left', Rotate_Left)

cdef PrimOp Rotate_Right = PrimOp()
Rotate_Right.po = c_Rotate_Right
setattr(primops, 'Rotate_Right', Rotate_Right)

cdef PrimOp BV_To_Nat = PrimOp()
BV_To_Nat.po = c_BV_To_Nat
setattr(primops, 'BV_To_Nat', BV_To_Nat)

cdef PrimOp Int_To_BV = PrimOp()
Int_To_BV.po = c_Int_To_BV
setattr(primops, 'Int_To_BV', Int_To_BV)

cdef PrimOp Select = PrimOp()
Select.po = c_Select
setattr(primops, 'Select', Select)

cdef PrimOp Store = PrimOp()
Store.po = c_Store
setattr(primops, 'Store', Store)

cdef PrimOp Forall = PrimOp()
Forall.po = c_Forall
setattr(primops, 'Forall', Forall)

cdef PrimOp Exists = PrimOp()
Exists.po = c_Exists
setattr(primops, 'Exists', Exists)

##################################### dictionaries for getting canonical enum objects ###################

int2primop = dict()
for attr in dir(primops):
    if not attr.startswith("_"):
        pypo = getattr(primops, attr)
        int2primop[(<int> (<PrimOp?> pypo).po)] = pypo

int2sortkind = dict()
for attr in dir(sortkinds):
    if not attr.startswith("_"):
        pysk = getattr(sortkinds, attr)
        int2sortkind[(<int> (<SortKind?> pysk).sk)] = pysk
