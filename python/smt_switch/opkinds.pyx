from .cppenums cimport (
    # Core
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
    # Arithmetic
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
    c_IntDiv,
    c_Divisible,
    # Conversions between integers and reals
    c_To_Real,
    c_To_Int,
    c_Is_Int,
    # Bit-vectors
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
    c_BVComp,
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
    # Conversions between bit-vectors and integers
    c_UBV_To_Int,
    c_SBV_To_Int,
    c_Int_To_BV,
    # Strings
    c_StrLt,
    c_StrLeq,
    c_StrLen,
    c_StrConcat,
    c_StrSubstr,
    c_StrAt,
    c_StrContains,
    c_StrIndexof,
    c_StrReplace,
    c_StrReplaceAll,
    c_StrPrefixof,
    c_StrSuffixof,
    c_StrIsDigit,
    # Arrays
    c_Select,
    c_Store,
    # Quantifiers
    c_Forall,
    c_Exists,
    # Datatypes
    c_Apply_Selector,
    c_Apply_Tester,
    c_Apply_Constructor,
)
from .enums cimport OpKind


cdef OpKind And = OpKind()
And.ck = c_And
globals()["And"] = And

cdef OpKind Or = OpKind()
Or.ck = c_Or
globals()["Or"] = Or

cdef OpKind Xor = OpKind()
Xor.ck = c_Xor
globals()["Xor"] = Xor

cdef OpKind Not = OpKind()
Not.ck = c_Not
globals()["Not"] = Not

cdef OpKind Implies = OpKind()
Implies.ck = c_Implies
globals()["Implies"] = Implies

cdef OpKind Ite = OpKind()
Ite.ck = c_Ite
globals()["Ite"] = Ite

cdef OpKind Equal = OpKind()
Equal.ck = c_Equal
globals()["Equal"] = Equal

cdef OpKind Distinct = OpKind()
Distinct.ck = c_Distinct
globals()["Distinct"] = Distinct

cdef OpKind Apply = OpKind()
Apply.ck = c_Apply
globals()["Apply"] = Apply

cdef OpKind Plus = OpKind()
Plus.ck = c_Plus
globals()["Plus"] = Plus

cdef OpKind Minus = OpKind()
Minus.ck = c_Minus
globals()["Minus"] = Minus

cdef OpKind Negate = OpKind()
Negate.ck = c_Negate
globals()["Negate"] = Negate

cdef OpKind Mult = OpKind()
Mult.ck = c_Mult
globals()["Mult"] = Mult

cdef OpKind Div = OpKind()
Div.ck = c_Div
globals()["Div"] = Div

cdef OpKind Lt = OpKind()
Lt.ck = c_Lt
globals()["Lt"] = Lt

cdef OpKind Le = OpKind()
Le.ck = c_Le
globals()["Le"] = Le

cdef OpKind Gt = OpKind()
Gt.ck = c_Gt
globals()["Gt"] = Gt

cdef OpKind Ge = OpKind()
Ge.ck = c_Ge
globals()["Ge"] = Ge

cdef OpKind Mod = OpKind()
Mod.ck = c_Mod
globals()["Mod"] = Mod

cdef OpKind Abs = OpKind()
Abs.ck = c_Abs
globals()["Abs"] = Abs

cdef OpKind Pow = OpKind()
Pow.ck = c_Pow
globals()["Pow"] = Pow

cdef OpKind IntDiv = OpKind()
IntDiv.ck = c_IntDiv
globals()["IntDiv"] = IntDiv

cdef OpKind Divisible = OpKind()
Divisible.ck = c_Divisible
globals()["Divisible"] = Divisible

cdef OpKind To_Real = OpKind()
To_Real.ck = c_To_Real
globals()["To_Real"] = To_Real

cdef OpKind To_Int = OpKind()
To_Int.ck = c_To_Int
globals()["To_Int"] = To_Int

cdef OpKind Is_Int = OpKind()
Is_Int.ck = c_Is_Int
globals()["Is_Int"] = Is_Int

cdef OpKind Concat = OpKind()
Concat.ck = c_Concat
globals()["Concat"] = Concat

cdef OpKind Extract = OpKind()
Extract.ck = c_Extract
globals()["Extract"] = Extract

cdef OpKind BVNot = OpKind()
BVNot.ck = c_BVNot
globals()["BVNot"] = BVNot

cdef OpKind BVNeg = OpKind()
BVNeg.ck = c_BVNeg
globals()["BVNeg"] = BVNeg

cdef OpKind BVAnd = OpKind()
BVAnd.ck = c_BVAnd
globals()["BVAnd"] = BVAnd

cdef OpKind BVOr = OpKind()
BVOr.ck = c_BVOr
globals()["BVOr"] = BVOr

cdef OpKind BVXor = OpKind()
BVXor.ck = c_BVXor
globals()["BVXor"] = BVXor

cdef OpKind BVNand = OpKind()
BVNand.ck = c_BVNand
globals()["BVNand"] = BVNand

cdef OpKind BVNor = OpKind()
BVNor.ck = c_BVNor
globals()["BVNor"] = BVNor

cdef OpKind BVXnor = OpKind()
BVXnor.ck = c_BVXnor
globals()["BVXnor"] = BVXnor

cdef OpKind BVAdd = OpKind()
BVAdd.ck = c_BVAdd
globals()["BVAdd"] = BVAdd

cdef OpKind BVSub = OpKind()
BVSub.ck = c_BVSub
globals()["BVSub"] = BVSub

cdef OpKind BVMul = OpKind()
BVMul.ck = c_BVMul
globals()["BVMul"] = BVMul

cdef OpKind BVUdiv = OpKind()
BVUdiv.ck = c_BVUdiv
globals()["BVUdiv"] = BVUdiv

cdef OpKind BVSdiv = OpKind()
BVSdiv.ck = c_BVSdiv
globals()["BVSdiv"] = BVSdiv

cdef OpKind BVUrem = OpKind()
BVUrem.ck = c_BVUrem
globals()["BVUrem"] = BVUrem

cdef OpKind BVSrem = OpKind()
BVSrem.ck = c_BVSrem
globals()["BVSrem"] = BVSrem

cdef OpKind BVSmod = OpKind()
BVSmod.ck = c_BVSmod
globals()["BVSmod"] = BVSmod

cdef OpKind BVShl = OpKind()
BVShl.ck = c_BVShl
globals()["BVShl"] = BVShl

cdef OpKind BVAshr = OpKind()
BVAshr.ck = c_BVAshr
globals()["BVAshr"] = BVAshr

cdef OpKind BVLshr = OpKind()
BVLshr.ck = c_BVLshr
globals()["BVLshr"] = BVLshr

cdef OpKind BVComp = OpKind()
BVComp.ck = c_BVComp
globals()["BVComp"] = BVComp

cdef OpKind BVUlt = OpKind()
BVUlt.ck = c_BVUlt
globals()["BVUlt"] = BVUlt

cdef OpKind BVUle = OpKind()
BVUle.ck = c_BVUle
globals()["BVUle"] = BVUle

cdef OpKind BVUgt = OpKind()
BVUgt.ck = c_BVUgt
globals()["BVUgt"] = BVUgt

cdef OpKind BVUge = OpKind()
BVUge.ck = c_BVUge
globals()["BVUge"] = BVUge

cdef OpKind BVSlt = OpKind()
BVSlt.ck = c_BVSlt
globals()["BVSlt"] = BVSlt

cdef OpKind BVSle = OpKind()
BVSle.ck = c_BVSle
globals()["BVSle"] = BVSle

cdef OpKind BVSgt = OpKind()
BVSgt.ck = c_BVSgt
globals()["BVSgt"] = BVSgt

cdef OpKind BVSge = OpKind()
BVSge.ck = c_BVSge
globals()["BVSge"] = BVSge

cdef OpKind Zero_Extend = OpKind()
Zero_Extend.ck = c_Zero_Extend
globals()["Zero_Extend"] = Zero_Extend

cdef OpKind Sign_Extend = OpKind()
Sign_Extend.ck = c_Sign_Extend
globals()["Sign_Extend"] = Sign_Extend

cdef OpKind Repeat = OpKind()
Repeat.ck = c_Repeat
globals()["Repeat"] = Repeat

cdef OpKind Rotate_Left = OpKind()
Rotate_Left.ck = c_Rotate_Left
globals()["Rotate_Left"] = Rotate_Left

cdef OpKind Rotate_Right = OpKind()
Rotate_Right.ck = c_Rotate_Right
globals()["Rotate_Right"] = Rotate_Right

cdef OpKind UBV_To_Int = OpKind()
UBV_To_Int.ck = c_UBV_To_Int
globals()["UBV_To_Int"] = UBV_To_Int

# the deprecated spelling of UBV_To_Int, as the same object
globals()["BV_To_Nat"] = UBV_To_Int

cdef OpKind SBV_To_Int = OpKind()
SBV_To_Int.ck = c_SBV_To_Int
globals()["SBV_To_Int"] = SBV_To_Int

cdef OpKind Int_To_BV = OpKind()
Int_To_BV.ck = c_Int_To_BV
globals()["Int_To_BV"] = Int_To_BV

cdef OpKind StrLt = OpKind()
StrLt.ck = c_StrLt
globals()["StrLt"] = StrLt

cdef OpKind StrLeq = OpKind()
StrLeq.ck = c_StrLeq
globals()["StrLeq"] = StrLeq

cdef OpKind StrLen = OpKind()
StrLen.ck = c_StrLen
globals()["StrLen"] = StrLen

cdef OpKind StrConcat = OpKind()
StrConcat.ck = c_StrConcat
globals()["StrConcat"] = StrConcat

cdef OpKind StrSubstr = OpKind()
StrSubstr.ck = c_StrSubstr
globals()["StrSubstr"] = StrSubstr

cdef OpKind StrAt = OpKind()
StrAt.ck = c_StrAt
globals()["StrAt"] = StrAt

cdef OpKind StrContains = OpKind()
StrContains.ck = c_StrContains
globals()["StrContains"] = StrContains

cdef OpKind StrIndexof = OpKind()
StrIndexof.ck = c_StrIndexof
globals()["StrIndexof"] = StrIndexof

cdef OpKind StrReplace = OpKind()
StrReplace.ck = c_StrReplace
globals()["StrReplace"] = StrReplace

cdef OpKind StrReplaceAll = OpKind()
StrReplaceAll.ck = c_StrReplaceAll
globals()["StrReplaceAll"] = StrReplaceAll

cdef OpKind StrPrefixof = OpKind()
StrPrefixof.ck = c_StrPrefixof
globals()["StrPrefixof"] = StrPrefixof

cdef OpKind StrSuffixof = OpKind()
StrSuffixof.ck = c_StrSuffixof
globals()["StrSuffixof"] = StrSuffixof

cdef OpKind StrIsDigit = OpKind()
StrIsDigit.ck = c_StrIsDigit
globals()["StrIsDigit"] = StrIsDigit

cdef OpKind Select = OpKind()
Select.ck = c_Select
globals()["Select"] = Select

cdef OpKind Store = OpKind()
Store.ck = c_Store
globals()["Store"] = Store

cdef OpKind Forall = OpKind()
Forall.ck = c_Forall
globals()["Forall"] = Forall

cdef OpKind Exists = OpKind()
Exists.ck = c_Exists
globals()["Exists"] = Exists

cdef OpKind Apply_Selector = OpKind()
Apply_Selector.ck = c_Apply_Selector
globals()["Apply_Selector"] = Apply_Selector

cdef OpKind Apply_Tester = OpKind()
Apply_Tester.ck = c_Apply_Tester
globals()["Apply_Tester"] = Apply_Tester

cdef OpKind Apply_Constructor = OpKind()
Apply_Constructor.ck = c_Apply_Constructor
globals()["Apply_Constructor"] = Apply_Constructor


attrs = {attr: pykind for attr, pykind in globals().items() if not attr.startswith("_")}
int2opkind = dict()
for pykind in attrs.values():
    int2opkind[(<int> (<OpKind?> pykind).ck)] = pykind
