/*!
 * \file ops.h
 * \brief All the builtin operators
 * \author Makai Mann
 * \author Clark Barrett
 * \date 2019
 * \copyright See the LICENSE file in the top-level source directory.
 */
#ifndef SMT_SWITCH_OPS_H
#define SMT_SWITCH_OPS_H

#ifndef SMT_SWITCH_INTERNAL
// IWYU pragma: private, include "smt-switch/smt.h"
#endif

#include <array>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <ostream>
#include <string>
#include <utility>

#include "smt-switch/smt_defs.h"

namespace smt {

/**
   Represents operators
   An Op made with indices is an indexed operator
 */
class Op
{
 public:
  /** The operators, named after their SMT-LIB symbols */
  enum Kind
  {
    NONE,  // no operator, as for a symbol or value
    // Core
    And,
    Or,
    Xor,
    Not,
    Implies,
    Ite,
    Equal,
    Distinct,
    // Uninterpreted functions
    Apply,
    // Arithmetic
    Plus,
    Minus,
    Negate,
    Mult,
    Div,
    Lt,
    Le,
    Gt,
    Ge,
    // Integers only
    Mod,
    Abs,
    Pow,
    IntDiv,
    Divisible,
    // Conversions between integers and reals
    To_Real,
    To_Int,
    Is_Int,
    // Bit-vectors
    Concat,
    Extract,
    BVNot,
    BVNeg,
    BVAnd,
    BVOr,
    BVXor,
    BVNand,
    BVNor,
    BVXnor,
    BVAdd,
    BVSub,
    BVMul,
    BVUdiv,
    BVSdiv,
    BVUrem,
    BVSrem,
    BVSmod,
    BVShl,
    BVAshr,
    BVLshr,
    BVComp,
    BVUlt,
    BVUle,
    BVUgt,
    BVUge,
    BVSlt,
    BVSle,
    BVSgt,
    BVSge,
    Zero_Extend,
    Sign_Extend,
    Repeat,
    Rotate_Left,
    Rotate_Right,
    // Conversions between bit-vectors and integers
    UBV_To_Int,
    BV_To_Nat [[deprecated("use UBV_To_Int")]] = UBV_To_Int,
    SBV_To_Int,
    Int_To_BV,
    // Strings
    StrLt,
    StrLeq,
    StrLen,
    StrConcat,
    StrSubstr,
    StrAt,
    StrContains,
    StrIndexof,
    StrReplace,
    StrReplaceAll,
    StrPrefixof,
    StrSuffixof,
    StrIsDigit,
    // Arrays
    Select,
    Store,
    // Quantifiers
    Forall,
    Exists,
    // Datatypes
    Apply_Selector,
    Apply_Tester,
    Apply_Constructor,
  };

  /** How many kinds there are, Op::NONE included */
  static constexpr std::size_t num_kinds = Apply_Constructor + 1;

  /** The SMT-LIB theory that declares an operator, or for an operator no
   *  theory declares, the part of SMT-LIB that provides it
   */
  enum class Theory
  {
    CORE,         ///< Core
    UF,           ///< function application
    ARITH,        ///< declared by both Ints and Reals
    INTS,         ///< Ints only
    REALS,        ///< Reals only
    REALS_INTS,   ///< the conversions that only Reals_Ints declares
    BITVECTORS,   ///< FixedSizeBitVectors and the QF_BV abbreviations
    STRINGS,      ///< UnicodeStrings
    ARRAYS,       ///< ArraysEx
    QUANTIFIERS,  ///< forall and exists
    DATATYPES,    ///< the constructors, selectors and testers of datatypes
  };

  /** The indices of an Op, in order, fixed when the Op is made: only Op can
   *  make one or assign to one
   */
  class Indices
  {
   public:
    Indices(const Indices & other) = default;
    std::size_t size() const;
    bool empty() const;
    /** @throws IncorrectUsageException at or past size() */
    std::uint64_t operator[](std::size_t i) const;
    const std::uint64_t * begin() const;
    const std::uint64_t * end() const;
    bool operator==(const Indices & other) const;
    bool operator!=(const Indices & other) const;

   private:
    friend class Op;
    Indices() = default;
    explicit Indices(std::uint64_t index0);
    Indices(std::uint64_t index0, std::uint64_t index1);
    Indices & operator=(const Indices & other) = default;
    // SMT-LIB indices are naturals, and no operator takes more than two.
    std::array<std::uint64_t, 2> values{};
    std::uint8_t count = 0;
  };

  Op() = default;
  /** @throws IncorrectUsageException for an operator that takes indices */
  Op(Kind k);
  /** @throws IncorrectUsageException for an operator that does not take one
   *  index
   */
  Op(Kind k, std::uint64_t index0);
  /** @throws IncorrectUsageException for an operator that does not take two
   *  indices
   */
  Op(Kind k, std::uint64_t index0, std::uint64_t index1);

  // Properties of the operator

  Kind kind() const;
  /** The fewest and most arguments the operator accepts
   *  @throws IncorrectUsageException for a null Op
   */
  std::pair<std::size_t, std::size_t> arity() const;
  /** The theory of the operator
   *  @throws IncorrectUsageException for a null Op
   */
  Theory theory() const;

  // Tests of the operator

  bool is_null() const;
  /** Whether the operator applies its first child, a function, constructor,
   *  selector or tester, to the others
   */
  bool is_apply() const;
  /* SMT-LIB defines the applications of some function symbols to more than
   * two arguments in terms of their applications to two, by giving them one
   * of the attributes below. Every backend takes these operators with any
   * number of arguments, and builds the applications to two itself where its
   * solver takes no more.
   */
  /** Whether the operator is :left-assoc, e.g. (- a b c) is (- (- a b) c)
   *  @throws IncorrectUsageException for a null Op
   */
  bool is_left_assoc() const;
  /** Whether the operator is :right-assoc, e.g. (=> a b c) is
   *  (=> a (=> b c))
   *  @throws IncorrectUsageException for a null Op
   */
  bool is_right_assoc() const;
  /** Whether the operator is :chainable, e.g. (< a b c) is
   *  (and (< a b) (< b c))
   *  @throws IncorrectUsageException for a null Op
   */
  bool is_chainable() const;
  /** Whether the operator is :pairwise, e.g. (distinct a b c) is
   *  (and (distinct a b) (distinct a c) (distinct b c))
   *  @throws IncorrectUsageException for a null Op
   */
  bool is_pairwise() const;
  /** Whether the operator can be applied to more than two arguments: whether
   *  it is :left-assoc, :right-assoc, :chainable or :pairwise
   *  @throws IncorrectUsageException for a null Op
   */
  bool is_variadic() const;

  // Printing

  std::string to_string() const;

  // Sort checking and inference for applications of the operator, defined
  // in sort_inference.cpp

  /** Checks if applying the operator to the terms is well-sorted
   *  @param terms the vector of terms to apply it to
   *  @return true iff this is a well-sorted operation
   */
  bool check_sortedness(const TermVec & terms) const;

  /** Checks if applying the operator to the terms of these sorts is
   *  well-sorted
   *  @param sorts the vector of sorts it would be applied to
   *  @return true iff this is a well-sorted operation
   */
  bool check_sortedness(const SortVec & sorts) const;

  /** Compute the expected sort of applying the operator to these terms
   *  @param solver the solver to use to make the new sort
   *         assumed that the passed sorts belong to this solver
   *  @param terms the vector of terms the op would be applied to
   *  @return the expected sort
   *  @throws IncorrectUsageException if there are fewer terms than the op
   *          accepts, the indices of an extract are outside its argument, or
   *          the resulting width does not fit in 64 bits
   */
  Sort compute_sort(const std::shared_ptr<const AbsSmtSolver> & solver,
                    const TermVec & terms) const;

  /** Compute the expected sort of applying the operator to terms of these
   *  sorts
   *  @param solver the solver to use to make the new sort
   *         assumed that the passed sorts belong to this solver
   *  @param sorts a vector of sorts corresponding to the op arguments
   *  @return the expected sort
   *  @throws IncorrectUsageException if there are fewer sorts than the op
   *          accepts, the indices of an extract are outside its argument, or
   *          the resulting width does not fit in 64 bits
   */
  Sort compute_sort(const std::shared_ptr<const AbsSmtSolver> & solver,
                    const SortVec & sorts) const;

  Indices indices = {};

 private:
  Kind kind_ = NONE;
};

std::string to_string(Op::Kind k);
std::ostream & operator<<(std::ostream & output, Op::Kind k);
bool operator==(Op o1, Op o2);
bool operator!=(Op o1, Op o2);
std::ostream & operator<<(std::ostream & output, const Op o);

}  // namespace smt

namespace std {
template <>
struct hash<smt::Op>
{
  size_t operator()(const smt::Op o) const;
};
}  // namespace std

#endif  // SMT_SWITCH_OPS_H
