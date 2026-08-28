# Sorts and operators

This document explains how smt-switch decides which operator applies to which
terms, and why the same `make_term` call can look different depending on the
backend. It exists because these questions come up repeatedly
([#320](https://github.com/stanford-centaur/smt-switch/issues/320)).

## Operators are not overloaded

smt-switch has a single flat enumeration of primitive operators
([`include/ops.h`](../include/ops.h)). Boolean and bit-vector operators are
**separate entries**, not one polymorphic operator that adapts to its arguments:

```cpp
And = 0,  // :36  boolean conjunction
Or,       // :37
...
BVAnd,    // :70  bit-vector conjunction
BVOr,     // :71
```

This differs from SMT-LIB, where overload resolution is part of the language, and
it is the first thing to internalise. `make_term(And, x, y)` is legal only when
`x` and `y` are boolean; for bit-vectors you must write `make_term(BVAnd, x, y)`.

The requirement is declared in
[`src/sort_inference.cpp`](../src/sort_inference.cpp):

```cpp
{ And,   bool_sorts   },   // :40  — arguments must be boolean
{ Or,    bool_sorts   },   // :41
{ Not,   bool_sorts   },   // :43
{ BVAnd, eq_bv_sorts  },   // :72  — arguments must be bit-vectors of equal width
{ BVOr,  eq_bv_sorts  },   // :73
```

`bool_sorts` and `eq_bv_sorts` are the predicates each operator imposes on its
arguments. Note that the bit-vector predicate requires *equal* widths, so
`BVAnd` on a 4-bit and an 8-bit term is rejected before it reaches the solver.

## Checking before building

Two free functions in [`include/sort_inference.h`](../include/sort_inference.h)
let you ask about an application without constructing it:

```cpp
bool check_sortedness(Op op, const TermVec & terms);   // is this application legal?
Sort compute_sort(Op op, const SmtSolver solver, const TermVec & terms);  // what sort results?
```

Both also take a `SortVec` instead of a `TermVec`, so you can test a candidate
operation using sorts alone — useful when enumerating or synthesising terms and
you do not want to pay for construction just to discover the application is
ill-sorted:

```cpp
// Is `BVAdd` applicable to two terms of these sorts, and what would it produce?
SortVec sorts { s->make_sort(BV, 8), s->make_sort(BV, 8) };
if (check_sortedness(BVAdd, sorts)) {
  Sort result = compute_sort(BVAdd, s, sorts);   // BV of width 8
}
```

Quantifiers need their own predicates, because their arguments are not uniformly
sorted the way an `And`'s are:

```cpp
bool check_quantifier_terms(const TermVec & terms);
bool check_quantifier_sorts(const SortVec & sorts);
```

## Why the same term prints differently on different backends

This is the question behind
[#320](https://github.com/stanford-centaur/smt-switch/issues/320): a term built
with `And` shows up as `bvand`, and the same code against another solver shows
`and`.

There are two separate causes, and the example at
[`examples/btor_qf_ufbv.cpp:8`](../examples/btor_qf_ufbv.cpp) names both:

```cpp
// Boolector aliases booleans and bitvectors of size one
// and also performs on-the-fly rewriting
// if you'd like to maintain the term structure, you can
// enable logging by passing true
SmtSolver s = BoolectorSolverFactory::create(false);
```

**Cause 1 — sort aliasing.** Boolector has no separate boolean sort. Asking it
for one returns a bit-vector sort of width 1
([`btor/src/boolector_solver.cpp:497`](../btor/src/boolector_solver.cpp)):

```cpp
Sort BoolectorSolver::make_sort(SortKind sk) const
{
  if (sk == BOOL)
  {
    return std::make_shared<BoolectorBVSort>
        (btor, boolector_bool_sort(btor), 1);
  }
```

So on Boolector, a `BOOL`-sorted term *is* a 1-bit bit-vector term. The same
equivalence appears in `get_value`, which handles both kinds together
([`boolector_solver.cpp:352`](../btor/src/boolector_solver.cpp)):

```cpp
if ((sk == BV) || (sk == BOOL))
```

When such a term is printed, the backend prints what it actually holds — a
bit-vector operation. On a solver with a native boolean sort, such as cvc5 or Z3,
the same smt-switch code produces a boolean term and prints as `and`.

**Cause 2 — on-the-fly rewriting.** Boolector simplifies as terms are built, so
the structure you get back need not match the structure you asked for, quite
apart from the sort question. A conditional written one way may come back
expressed another way.

### Preserving the term structure you built

If you need the term DAG to reflect what your code constructed — for traversal,
for comparison, or for printing — create the solver with logging enabled:

```cpp
SmtSolver s = BoolectorSolverFactory::create(true);   // note: true, not false
```

`LoggingSolver` ([`include/logging_solver.h`](../include/logging_solver.h))
*"wraps another SmtSolver and tracks the term DAG by wrapping sorts and terms and
performs hash-consing."* It keeps smt-switch's own view of the term alongside the
backend's, so the structure survives both sort aliasing and backend rewriting.
This is the recommended fix when the shape of a term matters to you, and it works
for any backend, not just Boolector.

The cost is memory and a level of indirection, which is why it is opt-in rather
than the default.

**What to rely on without logging.** `SortKind` is the portable notion: a term
created with `make_sort(BOOL)` has sort kind `BOOL` on every backend, and
`check_sortedness` answers the same way everywhere. The backend's printed form is
not portable and should not be parsed or compared across solvers.
`PrintingSolver` ([`include/printing_solver.h`](../include/printing_solver.h))
emits SMT-LIB at the smt-switch level and is the right tool when you want a
stable textual rendering rather than a stable in-memory DAG.

## Translating terms between solvers

A related case: moving a term from one solver to another with `TermTranslator`.
Because backends disagree as above, translation sometimes has to substitute one
operator for another. The permitted substitutions are explicit in
[`src/term_translator.cpp`](../src/term_translator.cpp):

```cpp
// boolean ops that can easily be represented with bit-vector operators
const std::unordered_map<PrimOp, PrimOp> bool_to_bv_ops({
    { And, BVAnd }, { Or, BVOr }, { Xor, BVXor }, { Not, BVNot }, { Equal, BVComp },
});

// bitvector ops that can easily be represented with boolean operators
const std::unordered_map<PrimOp, PrimOp> bv_to_bool_ops({
    { BVAnd, And }, { BVOr, Or }, { BVXor, Xor }, { BVNot, Not }, { BVComp, Equal },
});
```

These maps are deliberately small. They cover the operators whose 1-bit
bit-vector meaning coincides exactly with their boolean meaning; anything outside
them is not translated this way.

## Summary

| Question | Answer |
|---|---|
| Is `And` overloaded for bit-vectors? | No — `And` and `BVAnd` are distinct operators |
| How do I test legality before building? | `check_sortedness(op, sorts)` |
| How do I know the result sort? | `compute_sort(op, solver, sorts)` |
| Why does Boolector print `bvand`? | Its `BOOL` sort *is* a 1-bit bit-vector sort |
| Why doesn't my term keep its shape? | Boolector also rewrites on the fly |
| How do I preserve the structure I built? | Create the solver with logging: `create(true)` |
| What is portable across backends? | `SortKind`, and the answers of `check_sortedness` |
| What is not portable? | The backend's printed representation |
