from .cppenums cimport (
    # Core theory
    c_And,
    c_Or,
    c_Xor,
    c_Not,
    c_Implies,
    c_Ite,
    c_Equal,
    c_Distinct,
    # Uninterpreted functions
    c_Apply,
    # Arithmetic theories
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
)
from .enums cimport PrimOp


cdef PrimOp And = PrimOp()
And.po = c_And
globals()["And"] = And

cdef PrimOp Or = PrimOp()
Or.po = c_Or
globals()["Or"] = Or

cdef PrimOp Xor = PrimOp()
Xor.po = c_Xor
globals()["Xor"] = Xor

cdef PrimOp Not = PrimOp()
Not.po = c_Not
globals()["Not"] = Not

cdef PrimOp Implies = PrimOp()
Implies.po = c_Implies
globals()["Implies"] = Implies

cdef PrimOp Ite = PrimOp()
Ite.po = c_Ite
globals()["Ite"] = Ite

cdef PrimOp Equal = PrimOp()
Equal.po = c_Equal
globals()["Equal"] = Equal

cdef PrimOp Distinct = PrimOp()
Distinct.po = c_Distinct
globals()["Distinct"] = Distinct

cdef PrimOp Apply = PrimOp()
Apply.po = c_Apply
globals()["Apply"] = Apply

cdef PrimOp Plus = PrimOp()
Plus.po = c_Plus
globals()["Plus"] = Plus

cdef PrimOp Minus = PrimOp()
Minus.po = c_Minus
globals()["Minus"] = Minus

cdef PrimOp Negate = PrimOp()
Negate.po = c_Negate
globals()["Negate"] = Negate

cdef PrimOp Mult = PrimOp()
Mult.po = c_Mult
globals()["Mult"] = Mult

cdef PrimOp Div = PrimOp()
Div.po = c_Div
globals()["Div"] = Div

cdef PrimOp Lt = PrimOp()
Lt.po = c_Lt
globals()["Lt"] = Lt

cdef PrimOp Le = PrimOp()
Le.po = c_Le
globals()["Le"] = Le

cdef PrimOp Gt = PrimOp()
Gt.po = c_Gt
globals()["Gt"] = Gt

cdef PrimOp Ge = PrimOp()
Ge.po = c_Ge
globals()["Ge"] = Ge

cdef PrimOp Mod = PrimOp()
Mod.po = c_Mod
globals()["Mod"] = Mod

cdef PrimOp Abs = PrimOp()
Abs.po = c_Abs
globals()["Abs"] = Abs

cdef PrimOp Pow = PrimOp()
Pow.po = c_Pow
globals()["Pow"] = Pow

cdef PrimOp To_Real = PrimOp()
To_Real.po = c_To_Real
globals()["To_Real"] = To_Real

cdef PrimOp To_Int = PrimOp()
To_Int.po = c_To_Int
globals()["To_Int"] = To_Int

cdef PrimOp Is_Int = PrimOp()
Is_Int.po = c_Is_Int
globals()["Is_Int"] = Is_Int

cdef PrimOp Concat = PrimOp()
Concat.po = c_Concat
globals()["Concat"] = Concat

cdef PrimOp Extract = PrimOp()
Extract.po = c_Extract
globals()["Extract"] = Extract

cdef PrimOp BVNot = PrimOp()
BVNot.po = c_BVNot
globals()["BVNot"] = BVNot

cdef PrimOp BVNeg = PrimOp()
BVNeg.po = c_BVNeg
globals()["BVNeg"] = BVNeg

cdef PrimOp BVAnd = PrimOp()
BVAnd.po = c_BVAnd
globals()["BVAnd"] = BVAnd

cdef PrimOp BVOr = PrimOp()
BVOr.po = c_BVOr
globals()["BVOr"] = BVOr

cdef PrimOp BVXor = PrimOp()
BVXor.po = c_BVXor
globals()["BVXor"] = BVXor

cdef PrimOp BVNand = PrimOp()
BVNand.po = c_BVNand
globals()["BVNand"] = BVNand

cdef PrimOp BVNor = PrimOp()
BVNor.po = c_BVNor
globals()["BVNor"] = BVNor

cdef PrimOp BVXnor = PrimOp()
BVXnor.po = c_BVXnor
globals()["BVXnor"] = BVXnor

cdef PrimOp BVComp = PrimOp()
BVComp.po = c_BVComp
globals()["BVComp"] = BVComp

cdef PrimOp BVAdd = PrimOp()
BVAdd.po = c_BVAdd
globals()["BVAdd"] = BVAdd

cdef PrimOp BVSub = PrimOp()
BVSub.po = c_BVSub
globals()["BVSub"] = BVSub

cdef PrimOp BVMul = PrimOp()
BVMul.po = c_BVMul
globals()["BVMul"] = BVMul

cdef PrimOp BVUdiv = PrimOp()
BVUdiv.po = c_BVUdiv
globals()["BVUdiv"] = BVUdiv

cdef PrimOp BVSdiv = PrimOp()
BVSdiv.po = c_BVSdiv
globals()["BVSdiv"] = BVSdiv

cdef PrimOp BVUrem = PrimOp()
BVUrem.po = c_BVUrem
globals()["BVUrem"] = BVUrem

cdef PrimOp BVSrem = PrimOp()
BVSrem.po = c_BVSrem
globals()["BVSrem"] = BVSrem

cdef PrimOp BVSmod = PrimOp()
BVSmod.po = c_BVSmod
globals()["BVSmod"] = BVSmod

cdef PrimOp BVShl = PrimOp()
BVShl.po = c_BVShl
globals()["BVShl"] = BVShl

cdef PrimOp BVAshr = PrimOp()
BVAshr.po = c_BVAshr
globals()["BVAshr"] = BVAshr

cdef PrimOp BVLshr = PrimOp()
BVLshr.po = c_BVLshr
globals()["BVLshr"] = BVLshr

cdef PrimOp BVUlt = PrimOp()
BVUlt.po = c_BVUlt
globals()["BVUlt"] = BVUlt

cdef PrimOp BVUle = PrimOp()
BVUle.po = c_BVUle
globals()["BVUle"] = BVUle

cdef PrimOp BVUgt = PrimOp()
BVUgt.po = c_BVUgt
globals()["BVUgt"] = BVUgt

cdef PrimOp BVUge = PrimOp()
BVUge.po = c_BVUge
globals()["BVUge"] = BVUge

cdef PrimOp BVSlt = PrimOp()
BVSlt.po = c_BVSlt
globals()["BVSlt"] = BVSlt

cdef PrimOp BVSle = PrimOp()
BVSle.po = c_BVSle
globals()["BVSle"] = BVSle

cdef PrimOp BVSgt = PrimOp()
BVSgt.po = c_BVSgt
globals()["BVSgt"] = BVSgt

cdef PrimOp BVSge = PrimOp()
BVSge.po = c_BVSge
globals()["BVSge"] = BVSge

cdef PrimOp Zero_Extend = PrimOp()
Zero_Extend.po = c_Zero_Extend
globals()["Zero_Extend"] = Zero_Extend

cdef PrimOp Sign_Extend = PrimOp()
Sign_Extend.po = c_Sign_Extend
globals()["Sign_Extend"] = Sign_Extend

cdef PrimOp Repeat = PrimOp()
Repeat.po = c_Repeat
globals()["Repeat"] = Repeat

cdef PrimOp Rotate_Left = PrimOp()
Rotate_Left.po = c_Rotate_Left
globals()["Rotate_Left"] = Rotate_Left

cdef PrimOp Rotate_Right = PrimOp()
Rotate_Right.po = c_Rotate_Right
globals()["Rotate_Right"] = Rotate_Right

cdef PrimOp BV_To_Nat = PrimOp()
BV_To_Nat.po = c_BV_To_Nat
globals()["BV_To_Nat"] = BV_To_Nat

cdef PrimOp Int_To_BV = PrimOp()
Int_To_BV.po = c_Int_To_BV
globals()["Int_To_BV"] = Int_To_BV

cdef PrimOp Select = PrimOp()
Select.po = c_Select
globals()["Select"] = Select

cdef PrimOp Store = PrimOp()
Store.po = c_Store
globals()["Store"] = Store

cdef PrimOp Forall = PrimOp()
Forall.po = c_Forall
globals()["Forall"] = Forall

cdef PrimOp Exists = PrimOp()
Exists.po = c_Exists
globals()["Exists"] = Exists


attrs = {attr: pypo for attr, pypo in globals().items() if not attr.startswith("_")}
int2primop = dict()
for attr, pypo in attrs.items():
    int2primop[(<int> (<PrimOp?> pypo).po)] = pypo
