cdef extern from "include/ops.h" namespace "smt":
    cdef cppclass PrimOp:
        # TODO see if we could just declare them all here
        pass

    cdef cppclass SortKind:
        # TODO see if we could just declare them all here
        pass

# TODO try calling it c_PrimOp somewhere
cdef extern from "include/ops.h" namespace "smt":
    cdef PrimOp And
    cdef PrimOp Or
    cdef PrimOp Xor
    cdef PrimOp Not
    cdef PrimOp Implies
    cdef PrimOp Iff
    cdef PrimOp Ite
    cdef PrimOp Equal
    cdef PrimOp Distinct
    # Uninterpreted Functions
    cdef PrimOp Apply
    # Arithmetic Theories
    cdef PrimOp Plus
    cdef PrimOp Minus
    cdef PrimOp Negate
    cdef PrimOp Mult
    cdef PrimOp Div
    cdef PrimOp Lt
    cdef PrimOp Le
    cdef PrimOp Gt
    cdef PrimOp Ge
    # Integers only
    cdef PrimOp Mod
    cdef PrimOp Abs
    cdef PrimOp Pow
    # Int/Real Conversion and Queries
    cdef PrimOp To_Real
    cdef PrimOp To_Int
    cdef PrimOp Is_Int
    # Fixed Size BitVector Theory
    cdef PrimOp Concat
    cdef PrimOp Extract
    cdef PrimOp BVNot
    cdef PrimOp BVNeg
    cdef PrimOp BVAnd
    cdef PrimOp BVOr
    cdef PrimOp BVXor
    cdef PrimOp BVNand
    cdef PrimOp BVNor
    cdef PrimOp BVXnor
    cdef PrimOp BVComp
    cdef PrimOp BVAdd
    cdef PrimOp BVSub
    cdef PrimOp BVMul
    cdef PrimOp BVUdiv
    cdef PrimOp BVSdiv
    cdef PrimOp BVUrem
    cdef PrimOp BVSrem
    cdef PrimOp BVSmod
    cdef PrimOp BVShl
    cdef PrimOp BVAshr
    cdef PrimOp BVLshr
    cdef PrimOp BVUlt
    cdef PrimOp BVUle
    cdef PrimOp BVUgt
    cdef PrimOp BVUge
    cdef PrimOp BVSlt
    cdef PrimOp BVSle
    cdef PrimOp BVSgt
    cdef PrimOp BVSge
    cdef PrimOp Zero_Extend
    cdef PrimOp Sign_Extend
    cdef PrimOp Repeat
    cdef PrimOp Rotate_Left
    cdef PrimOp Rotate_Right
    # BitVector Conversion
    cdef PrimOp BV_To_Nat
    cdef PrimOp Int_To_BV
    # Array Theory
    cdef PrimOp Select
    cdef PrimOp Store
    cdef PrimOp Const_Array

cdef extern from "include/sort.h" namespace "smt":
    cdef SortKind ARRAY
    cdef SortKind BOOL
    cdef SortKind BV
    cdef SortKind INT
    cdef SortKind REAL
    cdef SortKind FUNCTION
