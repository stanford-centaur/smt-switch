cimport enums
import sys
from types import ModuleType


################################################ SortKind #################################################
cdef class SortKind:
    cdef enums.SortKind sk
    cdef str name
    def __cinit__(self, str name):
        self.name = name

    def __eq__(self, SortKind other):
        return (<int> self.sk) == (<int> other.sk)

    def __ne__(self, SortKind other):
        return (<int> self.sk) != (<int> other.sk)

    def __hash__(self):
        return hash((<int> self.sk, self.name))

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name

    def as_int(self):
        return <int> self.sk


# create a sortkinds submodule
sortkinds = ModuleType('sortkinds')
# fake a submodule for dotted imports, e.g. from smt_switch.prim_ops import And
sys.modules['%s.%s'%(__name__, sortkinds.__name__)] = sortkinds
# TODO: check this -- probably linked to module type name
sortkinds.__file__ = sortkinds.__name__ + ".py"

cdef SortKind ARRAY = SortKind('ARRAY')
ARRAY.sk = enums.ARRAY
setattr(sortkinds, 'ARRAY', ARRAY)

cdef SortKind BOOL = SortKind('BOOL')
BOOL.sk = enums.BOOL
setattr(sortkinds, 'BOOL', BOOL)

cdef SortKind BV = SortKind('BV')
BV.sk = enums.BV
setattr(sortkinds, 'BV', BV)

cdef SortKind INT = SortKind('INT')
INT.sk = enums.INT
setattr(sortkinds, 'INT', INT)

cdef SortKind REAL = SortKind('REAL')
REAL.sk = enums.REAL
setattr(sortkinds, 'REAL', REAL)

cdef SortKind FUNCTION = SortKind('FUNCTION')
FUNCTION.sk = enums.FUNCTION
setattr(sortkinds, 'FUNCTION', FUNCTION)


################################################ PrimOps #################################################
cdef class PrimOp:
    cdef enums.PrimOp po
    cdef str name
    def __cinit__(self, str name):
        self.name = name

    def __eq__(self, PrimOp other):
        return (<int> self.po) == (<int> other.po)

    def __ne__(self, PrimOp other):
        return (<int> self.po) != (<int> other.po)

    def __hash__(self):
        return hash((<int> self.po, self.name))

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name

    def as_int(self):
        return <int> self.po

# create a primops submodule
primops = ModuleType('primops')
# fake a submodule for dotted imports, e.g. from smt_switch.prim_ops import And
sys.modules['%s.%s'%(__name__, primops.__name__)] = primops
# TODO: check this -- probably linked to module type name
primops.__file__ = primops.__name__ + ".py"

cdef PrimOp And = PrimOp('And')
And.po = enums.And
setattr(primops, 'And', And)

cdef PrimOp Or = PrimOp('Or')
Or.po = enums.Or
setattr(primops, 'Or', Or)

cdef PrimOp Xor = PrimOp('Xor')
Xor.po = enums.Xor
setattr(primops, 'Xor', Xor)

cdef PrimOp Not = PrimOp('Not')
Not.po = enums.Not
setattr(primops, 'Not', Not)

cdef PrimOp Implies = PrimOp('Implies')
Implies.po = enums.Implies
setattr(primops, 'Implies', Implies)

cdef PrimOp Iff = PrimOp('Iff')
Iff.po = enums.Iff
setattr(primops, 'Iff', Iff)

cdef PrimOp Ite = PrimOp('Ite')
Ite.po = enums.Ite
setattr(primops, 'Ite', Ite)

cdef PrimOp Equal = PrimOp('Equal')
Equal.po = enums.Equal
setattr(primops, 'Equal', Equal)

cdef PrimOp Distinct = PrimOp('Distinct')
Distinct.po = enums.Distinct
setattr(primops, 'Distinct', Distinct)

cdef PrimOp Apply = PrimOp('Apply')
Apply.po = enums.Apply
setattr(primops, 'Apply', Apply)

cdef PrimOp Plus = PrimOp('Plus')
Plus.po = enums.Plus
setattr(primops, 'Plus', Plus)

cdef PrimOp Minus = PrimOp('Minus')
Minus.po = enums.Minus
setattr(primops, 'Minus', Minus)

cdef PrimOp Negate = PrimOp('Negate')
Negate.po = enums.Negate
setattr(primops, 'Negate', Negate)

cdef PrimOp Mult = PrimOp('Mult')
Mult.po = enums.Mult
setattr(primops, 'Mult', Mult)

cdef PrimOp Div = PrimOp('Div')
Div.po = enums.Div
setattr(primops, 'Div', Div)

cdef PrimOp Lt = PrimOp('Lt')
Lt.po = enums.Lt
setattr(primops, 'Lt', Lt)

cdef PrimOp Le = PrimOp('Le')
Le.po = enums.Le
setattr(primops, 'Le', Le)

cdef PrimOp Gt = PrimOp('Gt')
Gt.po = enums.Gt
setattr(primops, 'Gt', Gt)

cdef PrimOp Ge = PrimOp('Ge')
Ge.po = enums.Ge
setattr(primops, 'Ge', Ge)

cdef PrimOp Mod = PrimOp('Mod')
Mod.po = enums.Mod
setattr(primops, 'Mod', Mod)

cdef PrimOp Abs = PrimOp('Abs')
Abs.po = enums.Abs
setattr(primops, 'Abs', Abs)

cdef PrimOp Pow = PrimOp('Pow')
Pow.po = enums.Pow
setattr(primops, 'Pow', Pow)

cdef PrimOp To_Real = PrimOp('To_Real')
To_Real.po = enums.To_Real
setattr(primops, 'To_Real', To_Real)

cdef PrimOp To_Int = PrimOp('To_Int')
To_Int.po = enums.To_Int
setattr(primops, 'To_Int', To_Int)

cdef PrimOp Is_Int = PrimOp('Is_Int')
Is_Int.po = enums.Is_Int
setattr(primops, 'Is_Int', Is_Int)

cdef PrimOp Concat = PrimOp('Concat')
Concat.po = enums.Concat
setattr(primops, 'Concat', Concat)

cdef PrimOp Extract = PrimOp('Extract')
Extract.po = enums.Extract
setattr(primops, 'Extract', Extract)

cdef PrimOp BVNot = PrimOp('BVNot')
BVNot.po = enums.BVNot
setattr(primops, 'BVNot', BVNot)

cdef PrimOp BVNeg = PrimOp('BVNeg')
BVNeg.po = enums.BVNeg
setattr(primops, 'BVNeg', BVNeg)

cdef PrimOp BVAnd = PrimOp('BVAnd')
BVAnd.po = enums.BVAnd
setattr(primops, 'BVAnd', BVAnd)

cdef PrimOp BVOr = PrimOp('BVOr')
BVOr.po = enums.BVOr
setattr(primops, 'BVOr', BVOr)

cdef PrimOp BVXor = PrimOp('BVXor')
BVXor.po = enums.BVXor
setattr(primops, 'BVXor', BVXor)

cdef PrimOp BVNand = PrimOp('BVNand')
BVNand.po = enums.BVNand
setattr(primops, 'BVNand', BVNand)

cdef PrimOp BVNor = PrimOp('BVNor')
BVNor.po = enums.BVNor
setattr(primops, 'BVNor', BVNor)

cdef PrimOp BVXnor = PrimOp('BVXnor')
BVXnor.po = enums.BVXnor
setattr(primops, 'BVXnor', BVXnor)

cdef PrimOp BVComp = PrimOp('BVComp')
BVComp.po = enums.BVComp
setattr(primops, 'BVComp', BVComp)

cdef PrimOp BVAdd = PrimOp('BVAdd')
BVAdd.po = enums.BVAdd
setattr(primops, 'BVAdd', BVAdd)

cdef PrimOp BVSub = PrimOp('BVSub')
BVSub.po = enums.BVSub
setattr(primops, 'BVSub', BVSub)

cdef PrimOp BVMul = PrimOp('BVMul')
BVMul.po = enums.BVMul
setattr(primops, 'BVMul', BVMul)

cdef PrimOp BVUdiv = PrimOp('BVUdiv')
BVUdiv.po = enums.BVUdiv
setattr(primops, 'BVUdiv', BVUdiv)

cdef PrimOp BVSdiv = PrimOp('BVSdiv')
BVSdiv.po = enums.BVSdiv
setattr(primops, 'BVSdiv', BVSdiv)

cdef PrimOp BVUrem = PrimOp('BVUrem')
BVUrem.po = enums.BVUrem
setattr(primops, 'BVUrem', BVUrem)

cdef PrimOp BVSrem = PrimOp('BVSrem')
BVSrem.po = enums.BVSrem
setattr(primops, 'BVSrem', BVSrem)

cdef PrimOp BVSmod = PrimOp('BVSmod')
BVSmod.po = enums.BVSmod
setattr(primops, 'BVSmod', BVSmod)

cdef PrimOp BVShl = PrimOp('BVShl')
BVShl.po = enums.BVShl
setattr(primops, 'BVShl', BVShl)

cdef PrimOp BVAshr = PrimOp('BVAshr')
BVAshr.po = enums.BVAshr
setattr(primops, 'BVAshr', BVAshr)

cdef PrimOp BVLshr = PrimOp('BVLshr')
BVLshr.po = enums.BVLshr
setattr(primops, 'BVLshr', BVLshr)

cdef PrimOp BVUlt = PrimOp('BVUlt')
BVUlt.po = enums.BVUlt
setattr(primops, 'BVUlt', BVUlt)

cdef PrimOp BVUle = PrimOp('BVUle')
BVUle.po = enums.BVUle
setattr(primops, 'BVUle', BVUle)

cdef PrimOp BVUgt = PrimOp('BVUgt')
BVUgt.po = enums.BVUgt
setattr(primops, 'BVUgt', BVUgt)

cdef PrimOp BVUge = PrimOp('BVUge')
BVUge.po = enums.BVUge
setattr(primops, 'BVUge', BVUge)

cdef PrimOp BVSlt = PrimOp('BVSlt')
BVSlt.po = enums.BVSlt
setattr(primops, 'BVSlt', BVSlt)

cdef PrimOp BVSle = PrimOp('BVSle')
BVSle.po = enums.BVSle
setattr(primops, 'BVSle', BVSle)

cdef PrimOp BVSgt = PrimOp('BVSgt')
BVSgt.po = enums.BVSgt
setattr(primops, 'BVSgt', BVSgt)

cdef PrimOp BVSge = PrimOp('BVSge')
BVSge.po = enums.BVSge
setattr(primops, 'BVSge', BVSge)

cdef PrimOp Zero_Extend = PrimOp('Zero_Extend')
Zero_Extend.po = enums.Zero_Extend
setattr(primops, 'Zero_Extend', Zero_Extend)

cdef PrimOp Sign_Extend = PrimOp('Sign_Extend')
Sign_Extend.po = enums.Sign_Extend
setattr(primops, 'Sign_Extend', Sign_Extend)

cdef PrimOp Repeat = PrimOp('Repeat')
Repeat.po = enums.Repeat
setattr(primops, 'Repeat', Repeat)

cdef PrimOp Rotate_Left = PrimOp('Rotate_Left')
Rotate_Left.po = enums.Rotate_Left
setattr(primops, 'Rotate_Left', Rotate_Left)

cdef PrimOp Rotate_Right = PrimOp('Rotate_Right')
Rotate_Right.po = enums.Rotate_Right
setattr(primops, 'Rotate_Right', Rotate_Right)

cdef PrimOp BV_To_Nat = PrimOp('BV_To_Nat')
BV_To_Nat.po = enums.BV_To_Nat
setattr(primops, 'BV_To_Nat', BV_To_Nat)

cdef PrimOp Int_To_BV = PrimOp('Int_To_BV')
Int_To_BV.po = enums.Int_To_BV
setattr(primops, 'Int_To_BV', Int_To_BV)

cdef PrimOp Select = PrimOp('Select')
Select.po = enums.Select
setattr(primops, 'Select', Select)

cdef PrimOp Store = PrimOp('Store')
Store.po = enums.Store
setattr(primops, 'Store', Store)

cdef PrimOp Const_Array = PrimOp('Const_Array')
Const_Array.po = enums.Const_Array
setattr(primops, 'Const_Array', Const_Array)
