# distutils: language = c++
# distutils: extra_compile_args = -std=c++17

cimport ops
import sys
from types import ModuleType

cdef class PrimOp:
    cdef ops.PrimOp po
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
And.po = ops.And
setattr(primops, 'And', And)

cdef PrimOp Or = PrimOp('Or')
Or.po = ops.Or
setattr(primops, 'Or', Or)

cdef PrimOp Xor = PrimOp('Xor')
Xor.po = ops.Xor
setattr(primops, 'Xor', Xor)

cdef PrimOp Not = PrimOp('Not')
Not.po = ops.Not
setattr(primops, 'Not', Not)

cdef PrimOp Implies = PrimOp('Implies')
Implies.po = ops.Implies
setattr(primops, 'Implies', Implies)

cdef PrimOp Iff = PrimOp('Iff')
Iff.po = ops.Iff
setattr(primops, 'Iff', Iff)

cdef PrimOp Ite = PrimOp('Ite')
Ite.po = ops.Ite
setattr(primops, 'Ite', Ite)

cdef PrimOp Equal = PrimOp('Equal')
Equal.po = ops.Equal
setattr(primops, 'Equal', Equal)

cdef PrimOp Distinct = PrimOp('Distinct')
Distinct.po = ops.Distinct
setattr(primops, 'Distinct', Distinct)

cdef PrimOp Apply = PrimOp('Apply')
Apply.po = ops.Apply
setattr(primops, 'Apply', Apply)

cdef PrimOp Plus = PrimOp('Plus')
Plus.po = ops.Plus
setattr(primops, 'Plus', Plus)

cdef PrimOp Minus = PrimOp('Minus')
Minus.po = ops.Minus
setattr(primops, 'Minus', Minus)

cdef PrimOp Negate = PrimOp('Negate')
Negate.po = ops.Negate
setattr(primops, 'Negate', Negate)

cdef PrimOp Mult = PrimOp('Mult')
Mult.po = ops.Mult
setattr(primops, 'Mult', Mult)

cdef PrimOp Div = PrimOp('Div')
Div.po = ops.Div
setattr(primops, 'Div', Div)

cdef PrimOp Lt = PrimOp('Lt')
Lt.po = ops.Lt
setattr(primops, 'Lt', Lt)

cdef PrimOp Le = PrimOp('Le')
Le.po = ops.Le
setattr(primops, 'Le', Le)

cdef PrimOp Gt = PrimOp('Gt')
Gt.po = ops.Gt
setattr(primops, 'Gt', Gt)

cdef PrimOp Ge = PrimOp('Ge')
Ge.po = ops.Ge
setattr(primops, 'Ge', Ge)

cdef PrimOp Mod = PrimOp('Mod')
Mod.po = ops.Mod
setattr(primops, 'Mod', Mod)

cdef PrimOp Abs = PrimOp('Abs')
Abs.po = ops.Abs
setattr(primops, 'Abs', Abs)

cdef PrimOp Pow = PrimOp('Pow')
Pow.po = ops.Pow
setattr(primops, 'Pow', Pow)

cdef PrimOp To_Real = PrimOp('To_Real')
To_Real.po = ops.To_Real
setattr(primops, 'To_Real', To_Real)

cdef PrimOp To_Int = PrimOp('To_Int')
To_Int.po = ops.To_Int
setattr(primops, 'To_Int', To_Int)

cdef PrimOp Is_Int = PrimOp('Is_Int')
Is_Int.po = ops.Is_Int
setattr(primops, 'Is_Int', Is_Int)

cdef PrimOp Concat = PrimOp('Concat')
Concat.po = ops.Concat
setattr(primops, 'Concat', Concat)

cdef PrimOp Extract = PrimOp('Extract')
Extract.po = ops.Extract
setattr(primops, 'Extract', Extract)

cdef PrimOp BVNot = PrimOp('BVNot')
BVNot.po = ops.BVNot
setattr(primops, 'BVNot', BVNot)

cdef PrimOp BVNeg = PrimOp('BVNeg')
BVNeg.po = ops.BVNeg
setattr(primops, 'BVNeg', BVNeg)

cdef PrimOp BVAnd = PrimOp('BVAnd')
BVAnd.po = ops.BVAnd
setattr(primops, 'BVAnd', BVAnd)

cdef PrimOp BVOr = PrimOp('BVOr')
BVOr.po = ops.BVOr
setattr(primops, 'BVOr', BVOr)

cdef PrimOp BVXor = PrimOp('BVXor')
BVXor.po = ops.BVXor
setattr(primops, 'BVXor', BVXor)

cdef PrimOp BVNand = PrimOp('BVNand')
BVNand.po = ops.BVNand
setattr(primops, 'BVNand', BVNand)

cdef PrimOp BVNor = PrimOp('BVNor')
BVNor.po = ops.BVNor
setattr(primops, 'BVNor', BVNor)

cdef PrimOp BVXnor = PrimOp('BVXnor')
BVXnor.po = ops.BVXnor
setattr(primops, 'BVXnor', BVXnor)

cdef PrimOp BVComp = PrimOp('BVComp')
BVComp.po = ops.BVComp
setattr(primops, 'BVComp', BVComp)

cdef PrimOp BVAdd = PrimOp('BVAdd')
BVAdd.po = ops.BVAdd
setattr(primops, 'BVAdd', BVAdd)

cdef PrimOp BVSub = PrimOp('BVSub')
BVSub.po = ops.BVSub
setattr(primops, 'BVSub', BVSub)

cdef PrimOp BVMul = PrimOp('BVMul')
BVMul.po = ops.BVMul
setattr(primops, 'BVMul', BVMul)

cdef PrimOp BVUdiv = PrimOp('BVUdiv')
BVUdiv.po = ops.BVUdiv
setattr(primops, 'BVUdiv', BVUdiv)

cdef PrimOp BVSdiv = PrimOp('BVSdiv')
BVSdiv.po = ops.BVSdiv
setattr(primops, 'BVSdiv', BVSdiv)

cdef PrimOp BVUrem = PrimOp('BVUrem')
BVUrem.po = ops.BVUrem
setattr(primops, 'BVUrem', BVUrem)

cdef PrimOp BVSrem = PrimOp('BVSrem')
BVSrem.po = ops.BVSrem
setattr(primops, 'BVSrem', BVSrem)

cdef PrimOp BVSmod = PrimOp('BVSmod')
BVSmod.po = ops.BVSmod
setattr(primops, 'BVSmod', BVSmod)

cdef PrimOp BVShl = PrimOp('BVShl')
BVShl.po = ops.BVShl
setattr(primops, 'BVShl', BVShl)

cdef PrimOp BVAshr = PrimOp('BVAshr')
BVAshr.po = ops.BVAshr
setattr(primops, 'BVAshr', BVAshr)

cdef PrimOp BVLshr = PrimOp('BVLshr')
BVLshr.po = ops.BVLshr
setattr(primops, 'BVLshr', BVLshr)

cdef PrimOp BVUlt = PrimOp('BVUlt')
BVUlt.po = ops.BVUlt
setattr(primops, 'BVUlt', BVUlt)

cdef PrimOp BVUle = PrimOp('BVUle')
BVUle.po = ops.BVUle
setattr(primops, 'BVUle', BVUle)

cdef PrimOp BVUgt = PrimOp('BVUgt')
BVUgt.po = ops.BVUgt
setattr(primops, 'BVUgt', BVUgt)

cdef PrimOp BVUge = PrimOp('BVUge')
BVUge.po = ops.BVUge
setattr(primops, 'BVUge', BVUge)

cdef PrimOp BVSlt = PrimOp('BVSlt')
BVSlt.po = ops.BVSlt
setattr(primops, 'BVSlt', BVSlt)

cdef PrimOp BVSle = PrimOp('BVSle')
BVSle.po = ops.BVSle
setattr(primops, 'BVSle', BVSle)

cdef PrimOp BVSgt = PrimOp('BVSgt')
BVSgt.po = ops.BVSgt
setattr(primops, 'BVSgt', BVSgt)

cdef PrimOp BVSge = PrimOp('BVSge')
BVSge.po = ops.BVSge
setattr(primops, 'BVSge', BVSge)

cdef PrimOp Zero_Extend = PrimOp('Zero_Extend')
Zero_Extend.po = ops.Zero_Extend
setattr(primops, 'Zero_Extend', Zero_Extend)

cdef PrimOp Sign_Extend = PrimOp('Sign_Extend')
Sign_Extend.po = ops.Sign_Extend
setattr(primops, 'Sign_Extend', Sign_Extend)

cdef PrimOp Repeat = PrimOp('Repeat')
Repeat.po = ops.Repeat
setattr(primops, 'Repeat', Repeat)

cdef PrimOp Rotate_Left = PrimOp('Rotate_Left')
Rotate_Left.po = ops.Rotate_Left
setattr(primops, 'Rotate_Left', Rotate_Left)

cdef PrimOp Rotate_Right = PrimOp('Rotate_Right')
Rotate_Right.po = ops.Rotate_Right
setattr(primops, 'Rotate_Right', Rotate_Right)

cdef PrimOp BV_To_Nat = PrimOp('BV_To_Nat')
BV_To_Nat.po = ops.BV_To_Nat
setattr(primops, 'BV_To_Nat', BV_To_Nat)

cdef PrimOp Int_To_BV = PrimOp('Int_To_BV')
Int_To_BV.po = ops.Int_To_BV
setattr(primops, 'Int_To_BV', Int_To_BV)

cdef PrimOp Select = PrimOp('Select')
Select.po = ops.Select
setattr(primops, 'Select', Select)

cdef PrimOp Store = PrimOp('Store')
Store.po = ops.Store
setattr(primops, 'Store', Store)

cdef PrimOp Const_Array = PrimOp('Const_Array')
Const_Array.po = ops.Const_Array
setattr(primops, 'Const_Array', Const_Array)

