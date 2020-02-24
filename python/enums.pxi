cimport enums
import sys
from types import ModuleType


FILENAME="enums.pxi"

################################################ SortKind #################################################
cdef class SortKind:
    cdef enums.SortKind sk
    def __cinit__(self):
        pass

    def __eq__(self, SortKind other):
        return (<int> self.sk) == (<int> other.sk)

    def __ne__(self, SortKind other):
        return (<int> self.sk) != (<int> other.sk)

    def __hash__(self):
        return hash(<int> self.sk)

    def __str__(self):
        return enums.to_string(self.sk).decode()

    def __repr__(self):
        return enums.to_string(self.sk).decode()

    def as_int(self):
        return <int> self.sk


# create a sortkinds submodule
sortkinds = ModuleType('sortkinds')
# fake a submodule for dotted imports, e.g. from smt_switch.prim_ops import And
sys.modules['%s.%s'%(__name__, sortkinds.__name__)] = sortkinds
sortkinds.__file__ = FILENAME

cdef SortKind ARRAY = SortKind()
ARRAY.sk = enums.ARRAY
setattr(sortkinds, 'ARRAY', ARRAY)

cdef SortKind BOOL = SortKind()
BOOL.sk = enums.BOOL
setattr(sortkinds, 'BOOL', BOOL)

cdef SortKind BV = SortKind()
BV.sk = enums.BV
setattr(sortkinds, 'BV', BV)

cdef SortKind INT = SortKind()
INT.sk = enums.INT
setattr(sortkinds, 'INT', INT)

cdef SortKind REAL = SortKind()
REAL.sk = enums.REAL
setattr(sortkinds, 'REAL', REAL)

cdef SortKind FUNCTION = SortKind()
FUNCTION.sk = enums.FUNCTION
setattr(sortkinds, 'FUNCTION', FUNCTION)


################################################ PrimOps #################################################
cdef class PrimOp:
    cdef enums.PrimOp po
    def __cinit__(self):
        pass

    def __eq__(self, PrimOp other):
        return (<int> self.po) == (<int> other.po)

    def __ne__(self, PrimOp other):
        return (<int> self.po) != (<int> other.po)

    def __hash__(self):
        return hash((<int> self.po, self.name))

    def __str__(self):
        return enums.to_string(self.po).decode()

    def __repr__(self):
        return enums.to_string(self.po).decode()

    def as_int(self):
        return <int> self.po

# create a primops submodule
primops = ModuleType('primops')
# fake a submodule for dotted imports, e.g. from smt_switch.prim_ops import And
sys.modules['%s.%s'%(__name__, primops.__name__)] = primops
primops.__file__ = FILENAME + ".so"

cdef PrimOp And = PrimOp()
And.po = enums.And
setattr(primops, 'And', And)

cdef PrimOp Or = PrimOp()
Or.po = enums.Or
setattr(primops, 'Or', Or)

cdef PrimOp Xor = PrimOp()
Xor.po = enums.Xor
setattr(primops, 'Xor', Xor)

cdef PrimOp Not = PrimOp()
Not.po = enums.Not
setattr(primops, 'Not', Not)

cdef PrimOp Implies = PrimOp()
Implies.po = enums.Implies
setattr(primops, 'Implies', Implies)

cdef PrimOp Iff = PrimOp()
Iff.po = enums.Iff
setattr(primops, 'Iff', Iff)

cdef PrimOp Ite = PrimOp()
Ite.po = enums.Ite
setattr(primops, 'Ite', Ite)

cdef PrimOp Equal = PrimOp()
Equal.po = enums.Equal
setattr(primops, 'Equal', Equal)

cdef PrimOp Distinct = PrimOp()
Distinct.po = enums.Distinct
setattr(primops, 'Distinct', Distinct)

cdef PrimOp Apply = PrimOp()
Apply.po = enums.Apply
setattr(primops, 'Apply', Apply)

cdef PrimOp Plus = PrimOp()
Plus.po = enums.Plus
setattr(primops, 'Plus', Plus)

cdef PrimOp Minus = PrimOp()
Minus.po = enums.Minus
setattr(primops, 'Minus', Minus)

cdef PrimOp Negate = PrimOp()
Negate.po = enums.Negate
setattr(primops, 'Negate', Negate)

cdef PrimOp Mult = PrimOp()
Mult.po = enums.Mult
setattr(primops, 'Mult', Mult)

cdef PrimOp Div = PrimOp()
Div.po = enums.Div
setattr(primops, 'Div', Div)

cdef PrimOp Lt = PrimOp()
Lt.po = enums.Lt
setattr(primops, 'Lt', Lt)

cdef PrimOp Le = PrimOp()
Le.po = enums.Le
setattr(primops, 'Le', Le)

cdef PrimOp Gt = PrimOp()
Gt.po = enums.Gt
setattr(primops, 'Gt', Gt)

cdef PrimOp Ge = PrimOp()
Ge.po = enums.Ge
setattr(primops, 'Ge', Ge)

cdef PrimOp Mod = PrimOp()
Mod.po = enums.Mod
setattr(primops, 'Mod', Mod)

cdef PrimOp Abs = PrimOp()
Abs.po = enums.Abs
setattr(primops, 'Abs', Abs)

cdef PrimOp Pow = PrimOp()
Pow.po = enums.Pow
setattr(primops, 'Pow', Pow)

cdef PrimOp To_Real = PrimOp()
To_Real.po = enums.To_Real
setattr(primops, 'To_Real', To_Real)

cdef PrimOp To_Int = PrimOp()
To_Int.po = enums.To_Int
setattr(primops, 'To_Int', To_Int)

cdef PrimOp Is_Int = PrimOp()
Is_Int.po = enums.Is_Int
setattr(primops, 'Is_Int', Is_Int)

cdef PrimOp Concat = PrimOp()
Concat.po = enums.Concat
setattr(primops, 'Concat', Concat)

cdef PrimOp Extract = PrimOp()
Extract.po = enums.Extract
setattr(primops, 'Extract', Extract)

cdef PrimOp BVNot = PrimOp()
BVNot.po = enums.BVNot
setattr(primops, 'BVNot', BVNot)

cdef PrimOp BVNeg = PrimOp()
BVNeg.po = enums.BVNeg
setattr(primops, 'BVNeg', BVNeg)

cdef PrimOp BVAnd = PrimOp()
BVAnd.po = enums.BVAnd
setattr(primops, 'BVAnd', BVAnd)

cdef PrimOp BVOr = PrimOp()
BVOr.po = enums.BVOr
setattr(primops, 'BVOr', BVOr)

cdef PrimOp BVXor = PrimOp()
BVXor.po = enums.BVXor
setattr(primops, 'BVXor', BVXor)

cdef PrimOp BVNand = PrimOp()
BVNand.po = enums.BVNand
setattr(primops, 'BVNand', BVNand)

cdef PrimOp BVNor = PrimOp()
BVNor.po = enums.BVNor
setattr(primops, 'BVNor', BVNor)

cdef PrimOp BVXnor = PrimOp()
BVXnor.po = enums.BVXnor
setattr(primops, 'BVXnor', BVXnor)

cdef PrimOp BVComp = PrimOp()
BVComp.po = enums.BVComp
setattr(primops, 'BVComp', BVComp)

cdef PrimOp BVAdd = PrimOp()
BVAdd.po = enums.BVAdd
setattr(primops, 'BVAdd', BVAdd)

cdef PrimOp BVSub = PrimOp()
BVSub.po = enums.BVSub
setattr(primops, 'BVSub', BVSub)

cdef PrimOp BVMul = PrimOp()
BVMul.po = enums.BVMul
setattr(primops, 'BVMul', BVMul)

cdef PrimOp BVUdiv = PrimOp()
BVUdiv.po = enums.BVUdiv
setattr(primops, 'BVUdiv', BVUdiv)

cdef PrimOp BVSdiv = PrimOp()
BVSdiv.po = enums.BVSdiv
setattr(primops, 'BVSdiv', BVSdiv)

cdef PrimOp BVUrem = PrimOp()
BVUrem.po = enums.BVUrem
setattr(primops, 'BVUrem', BVUrem)

cdef PrimOp BVSrem = PrimOp()
BVSrem.po = enums.BVSrem
setattr(primops, 'BVSrem', BVSrem)

cdef PrimOp BVSmod = PrimOp()
BVSmod.po = enums.BVSmod
setattr(primops, 'BVSmod', BVSmod)

cdef PrimOp BVShl = PrimOp()
BVShl.po = enums.BVShl
setattr(primops, 'BVShl', BVShl)

cdef PrimOp BVAshr = PrimOp()
BVAshr.po = enums.BVAshr
setattr(primops, 'BVAshr', BVAshr)

cdef PrimOp BVLshr = PrimOp()
BVLshr.po = enums.BVLshr
setattr(primops, 'BVLshr', BVLshr)

cdef PrimOp BVUlt = PrimOp()
BVUlt.po = enums.BVUlt
setattr(primops, 'BVUlt', BVUlt)

cdef PrimOp BVUle = PrimOp()
BVUle.po = enums.BVUle
setattr(primops, 'BVUle', BVUle)

cdef PrimOp BVUgt = PrimOp()
BVUgt.po = enums.BVUgt
setattr(primops, 'BVUgt', BVUgt)

cdef PrimOp BVUge = PrimOp()
BVUge.po = enums.BVUge
setattr(primops, 'BVUge', BVUge)

cdef PrimOp BVSlt = PrimOp()
BVSlt.po = enums.BVSlt
setattr(primops, 'BVSlt', BVSlt)

cdef PrimOp BVSle = PrimOp()
BVSle.po = enums.BVSle
setattr(primops, 'BVSle', BVSle)

cdef PrimOp BVSgt = PrimOp()
BVSgt.po = enums.BVSgt
setattr(primops, 'BVSgt', BVSgt)

cdef PrimOp BVSge = PrimOp()
BVSge.po = enums.BVSge
setattr(primops, 'BVSge', BVSge)

cdef PrimOp Zero_Extend = PrimOp()
Zero_Extend.po = enums.Zero_Extend
setattr(primops, 'Zero_Extend', Zero_Extend)

cdef PrimOp Sign_Extend = PrimOp()
Sign_Extend.po = enums.Sign_Extend
setattr(primops, 'Sign_Extend', Sign_Extend)

cdef PrimOp Repeat = PrimOp()
Repeat.po = enums.Repeat
setattr(primops, 'Repeat', Repeat)

cdef PrimOp Rotate_Left = PrimOp()
Rotate_Left.po = enums.Rotate_Left
setattr(primops, 'Rotate_Left', Rotate_Left)

cdef PrimOp Rotate_Right = PrimOp()
Rotate_Right.po = enums.Rotate_Right
setattr(primops, 'Rotate_Right', Rotate_Right)

cdef PrimOp BV_To_Nat = PrimOp()
BV_To_Nat.po = enums.BV_To_Nat
setattr(primops, 'BV_To_Nat', BV_To_Nat)

cdef PrimOp Int_To_BV = PrimOp()
Int_To_BV.po = enums.Int_To_BV
setattr(primops, 'Int_To_BV', Int_To_BV)

cdef PrimOp Select = PrimOp()
Select.po = enums.Select
setattr(primops, 'Select', Select)

cdef PrimOp Store = PrimOp()
Store.po = enums.Store
setattr(primops, 'Store', Store)
