from libcpp.string cimport string

cdef extern from "smt-switch/ops.h" namespace "smt":
    cdef cppclass c_SortKind "smt::SortKind":
        pass

    cdef cppclass c_OpKind "smt::Op::Kind":
        pass


cdef extern from "smt-switch/sort.h" namespace "smt":
    cdef c_SortKind c_ARRAY "smt::SortKind::ARRAY"
    cdef c_SortKind c_BOOL "smt::SortKind::BOOL"
    cdef c_SortKind c_BV "smt::SortKind::BV"
    cdef c_SortKind c_INT "smt::SortKind::INT"
    cdef c_SortKind c_REAL "smt::SortKind::REAL"
    cdef c_SortKind c_STRING "smt::SortKind::STRING"
    cdef c_SortKind c_FUNCTION "smt::SortKind::FUNCTION"
    cdef c_SortKind c_UNINTERPRETED "smt::SortKind::UNINTERPRETED"
    cdef c_SortKind c_UNINTERPRETED_CONS "smt::SortKind::UNINTERPRETED_CONS"
    cdef c_SortKind c_DATATYPE "smt::SortKind::DATATYPE"
    cdef c_SortKind c_CONSTRUCTOR "smt::SortKind::CONSTRUCTOR"
    cdef c_SortKind c_SELECTOR "smt::SortKind::SELECTOR"
    cdef c_SortKind c_TESTER "smt::SortKind::TESTER"
    string to_string(c_SortKind sk) except +


cdef extern from "smt-switch/solver_enums.h" namespace "smt::solvers":
    cdef cppclass c_SolverKind "smt::solvers::Kind":
        pass

    cdef c_SolverKind c_BTOR "smt::solvers::BTOR"
    cdef c_SolverKind c_BZLA "smt::solvers::BZLA"
    cdef c_SolverKind c_CVC5 "smt::solvers::CVC5"
    cdef c_SolverKind c_GENERIC "smt::solvers::GENERIC"
    cdef c_SolverKind c_MSAT "smt::solvers::MSAT"
    cdef c_SolverKind c_YICES2 "smt::solvers::YICES2"
    cdef c_SolverKind c_Z3 "smt::solvers::Z3"

    string to_string(c_SolverKind kind) except +


cdef extern from "smt-switch/solver_enums.h" namespace "smt::interpolators":
    cdef cppclass c_InterpolatorKind "smt::interpolators::Kind":
        pass

    cdef c_InterpolatorKind c_BZLA_INTERPOLATOR "smt::interpolators::BZLA"
    cdef c_InterpolatorKind c_CVC5_INTERPOLATOR "smt::interpolators::CVC5"
    cdef c_InterpolatorKind c_MSAT_INTERPOLATOR "smt::interpolators::MSAT"
    cdef c_InterpolatorKind c_YICES2_INTERPOLATOR "smt::interpolators::YICES2"

    string to_string(c_InterpolatorKind kind) except +


cdef extern from "smt-switch/ops.h" namespace "smt":
    cdef c_OpKind c_And "smt::Op::And"
    cdef c_OpKind c_Or "smt::Op::Or"
    cdef c_OpKind c_Xor "smt::Op::Xor"
    cdef c_OpKind c_Not "smt::Op::Not"
    cdef c_OpKind c_Implies "smt::Op::Implies"
    cdef c_OpKind c_Ite "smt::Op::Ite"
    cdef c_OpKind c_Equal "smt::Op::Equal"
    cdef c_OpKind c_Distinct "smt::Op::Distinct"

    cdef c_OpKind c_Apply "smt::Op::Apply"

    cdef c_OpKind c_Plus "smt::Op::Plus"
    cdef c_OpKind c_Minus "smt::Op::Minus"
    cdef c_OpKind c_Negate "smt::Op::Negate"
    cdef c_OpKind c_Mult "smt::Op::Mult"
    cdef c_OpKind c_Div "smt::Op::Div"
    cdef c_OpKind c_Lt "smt::Op::Lt"
    cdef c_OpKind c_Le "smt::Op::Le"
    cdef c_OpKind c_Gt "smt::Op::Gt"
    cdef c_OpKind c_Ge "smt::Op::Ge"

    cdef c_OpKind c_Mod "smt::Op::Mod"
    cdef c_OpKind c_Abs "smt::Op::Abs"
    cdef c_OpKind c_Pow "smt::Op::Pow"
    cdef c_OpKind c_IntDiv "smt::Op::IntDiv"
    cdef c_OpKind c_Divisible "smt::Op::Divisible"

    cdef c_OpKind c_To_Real "smt::Op::To_Real"
    cdef c_OpKind c_To_Int "smt::Op::To_Int"
    cdef c_OpKind c_Is_Int "smt::Op::Is_Int"

    cdef c_OpKind c_Concat "smt::Op::Concat"
    cdef c_OpKind c_Extract "smt::Op::Extract"
    cdef c_OpKind c_BVNot "smt::Op::BVNot"
    cdef c_OpKind c_BVNeg "smt::Op::BVNeg"
    cdef c_OpKind c_BVAnd "smt::Op::BVAnd"
    cdef c_OpKind c_BVOr "smt::Op::BVOr"
    cdef c_OpKind c_BVXor "smt::Op::BVXor"
    cdef c_OpKind c_BVNand "smt::Op::BVNand"
    cdef c_OpKind c_BVNor "smt::Op::BVNor"
    cdef c_OpKind c_BVXnor "smt::Op::BVXnor"
    cdef c_OpKind c_BVAdd "smt::Op::BVAdd"
    cdef c_OpKind c_BVSub "smt::Op::BVSub"
    cdef c_OpKind c_BVMul "smt::Op::BVMul"
    cdef c_OpKind c_BVUdiv "smt::Op::BVUdiv"
    cdef c_OpKind c_BVSdiv "smt::Op::BVSdiv"
    cdef c_OpKind c_BVUrem "smt::Op::BVUrem"
    cdef c_OpKind c_BVSrem "smt::Op::BVSrem"
    cdef c_OpKind c_BVSmod "smt::Op::BVSmod"
    cdef c_OpKind c_BVShl "smt::Op::BVShl"
    cdef c_OpKind c_BVAshr "smt::Op::BVAshr"
    cdef c_OpKind c_BVLshr "smt::Op::BVLshr"
    cdef c_OpKind c_BVComp "smt::Op::BVComp"
    cdef c_OpKind c_BVUlt "smt::Op::BVUlt"
    cdef c_OpKind c_BVUle "smt::Op::BVUle"
    cdef c_OpKind c_BVUgt "smt::Op::BVUgt"
    cdef c_OpKind c_BVUge "smt::Op::BVUge"
    cdef c_OpKind c_BVSlt "smt::Op::BVSlt"
    cdef c_OpKind c_BVSle "smt::Op::BVSle"
    cdef c_OpKind c_BVSgt "smt::Op::BVSgt"
    cdef c_OpKind c_BVSge "smt::Op::BVSge"
    cdef c_OpKind c_Zero_Extend "smt::Op::Zero_Extend"
    cdef c_OpKind c_Sign_Extend "smt::Op::Sign_Extend"
    cdef c_OpKind c_Repeat "smt::Op::Repeat"
    cdef c_OpKind c_Rotate_Left "smt::Op::Rotate_Left"
    cdef c_OpKind c_Rotate_Right "smt::Op::Rotate_Right"

    cdef c_OpKind c_UBV_To_Int "smt::Op::UBV_To_Int"
    cdef c_OpKind c_SBV_To_Int "smt::Op::SBV_To_Int"
    cdef c_OpKind c_Int_To_BV "smt::Op::Int_To_BV"

    cdef c_OpKind c_StrLt "smt::Op::StrLt"
    cdef c_OpKind c_StrLeq "smt::Op::StrLeq"
    cdef c_OpKind c_StrLen "smt::Op::StrLen"
    cdef c_OpKind c_StrConcat "smt::Op::StrConcat"
    cdef c_OpKind c_StrSubstr "smt::Op::StrSubstr"
    cdef c_OpKind c_StrAt "smt::Op::StrAt"
    cdef c_OpKind c_StrContains "smt::Op::StrContains"
    cdef c_OpKind c_StrIndexof "smt::Op::StrIndexof"
    cdef c_OpKind c_StrReplace "smt::Op::StrReplace"
    cdef c_OpKind c_StrReplaceAll "smt::Op::StrReplaceAll"
    cdef c_OpKind c_StrPrefixof "smt::Op::StrPrefixof"
    cdef c_OpKind c_StrSuffixof "smt::Op::StrSuffixof"
    cdef c_OpKind c_StrIsDigit "smt::Op::StrIsDigit"

    cdef c_OpKind c_Select "smt::Op::Select"
    cdef c_OpKind c_Store "smt::Op::Store"

    cdef c_OpKind c_Forall "smt::Op::Forall"
    cdef c_OpKind c_Exists "smt::Op::Exists"

    cdef c_OpKind c_Apply_Selector "smt::Op::Apply_Selector"
    cdef c_OpKind c_Apply_Tester "smt::Op::Apply_Tester"
    cdef c_OpKind c_Apply_Constructor "smt::Op::Apply_Constructor"
    string to_string(c_OpKind op) except +
