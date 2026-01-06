/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Basic
public import Lean.Meta.Sym.AlphaShareCommon
public import Lean.Meta.CongrTheorems
public section
namespace Lean.Meta.Sym

register_builtin_option sym.debug : Bool := {
  defValue := false
  descr    := "check invariants"
}

/--
Information about a single argument position in a function's type signature.

This is used during pattern matching and structural definitional equality tests
to identify arguments that can be skipped or handled specially
(e.g., instance arguments can be synthesized, proof arguments can be inferred).
-/
public structure ProofInstArgInfo where
  /-- `true` if this argument is a proof (its type is a `Prop`). -/
  isProof    : Bool
  /-- `true` if this argument is a type class instance. -/
  isInstance : Bool
  deriving Inhabited

/--
Information about a function symbol. It stores which argument positions are proofs or instances,
enabling optimizations during pattern matching and structural definitional equality tests
such as skipping proof arguments or deferring instance synthesis.
-/
public structure ProofInstInfo where
  /-- Information about each argument position. -/
  argsInfo : Array ProofInstArgInfo
  deriving Inhabited

/--
Information on how to build congruence proofs for function applications.
This enables efficient rewriting of subterms without repeatedly inferring types or instances.
-/
inductive CongrInfo where
  | /-- None of the arguments of the function can be rewritten. -/
    none
  | /--
    For functions with a fixed prefix of implicit/instance arguments followed by
    explicit non-dependent arguments that can be rewritten independently.

    - `prefixSize`: Number of leading arguments (types, instances) that are determined
      by the suffix arguments and should not be rewritten directly.
    - `suffixSize`: Number of trailing arguments that can be rewritten using simple congruence.

    Examples (showing `prefixSize`, `suffixSize`):
    - `HAdd.hAdd {α β γ} [HAdd α β γ] (a : α) (b : β)`: `(4, 2)` — rewrite `a` and `b`
    - `And (p q : Prop)`: `(0, 2)` — rewrite both propositions
    - `Eq {α} (a b : α)`: `(1, 2)` — rewrite `a` and `b`, type `α` is fixed
    - `Neg.neg {α} [Neg α] (a : α)`: `(2, 1)` — rewrite just `a`
    -/
    fixedPrefix (prefixSize : Nat) (suffixSize : Nat)
  | /--
    For functions with interlaced rewritable and non-rewritable arguments.
    Each element indicates whether the corresponding argument position can be rewritten.

    Example: For `HEq {α : Sort u} (a : α) {β : Sort u} (b : β)`, the mask would be
    `#[false, true, false, true]` — we can rewrite `a` and `b`, but not `α` or `β`.
    -/
    interlaced (rewritable : Array Bool)
  | /--
    For functions that have proofs and `Decidable` arguments. For this kind of function we generate
    a custom theorem.
    Example: `Array.eraseIdx {α : Type u} (xs : Array α) (i : Nat) (h : i < xs.size) : Array α`.
    The proof argument `h` depends on `xs` and `i`. To be able to rewrite `xs` and `i`, we use the
    auto-generated theorem.
    ```
    Array.eraseIdx.congr_simp {α : Type u} (xs xs' : Array α) (e_xs : xs = xs')
        (i i' : Nat) (e_i : i = i') (h : i < xs.size) : xs.eraseIdx i h = xs'.eraseIdx i' ⋯
    ```
    -/
    congrTheorem (thm : CongrTheorem)

/-- Mutable state for the symbolic simulator framework. -/
structure State where
  /-- `ShareCommon` (aka `Hash-consing`) state. -/
  share : AlphaShareCommon.State := {}
  /--
  Maps expressions to their maximal free variable (by declaration index).

  - `maxFVar[e] = some fvarId` means `fvarId` is the free variable with the largest declaration
    index occurring in `e`.
  - `maxFVar[e] = none` means `e` contains no free variables (but may contain metavariables).

  Recall that if `e` contains a metavariable `?m`, then we assume `e` may contain any free variable
  in the local context associated with `?m`.

  This mapping enables O(1) local context compatibility checks during metavariable assignment.
  Instead of traversing local contexts with `isSubPrefixOf`, we check if the maximal free variable
  in the assigned value is in scope of the metavariable's local context.

  **Note**: We considered using a mapping `PHashMap ExprPtr FVarId`. However, there is a corner
  case that is not supported by this representation. `e` contains a metavariable (with an empty local context),
  and no free variables.
  -/
  maxFVar : PHashMap ExprPtr (Option FVarId) := {}
  proofInstInfo : PHashMap Name (Option ProofInstInfo) := {}
  /--
  Cache for `inferType` results, keyed by pointer equality.
  `SymM` uses a fixed configuration, so we can use a simpler key than `MetaM`.
  Remark: type inference is a bottleneck on `Meta.Tactic.Simp` simplifier.
  -/
  inferType : PHashMap ExprPtr Expr := {}
  /--
  Cache for `getLevel` results, keyed by pointer equality.
  -/
  getLevel : PHashMap ExprPtr Level := {}
  congrInfo : PHashMap ExprPtr CongrInfo := {}
  debug : Bool := false

abbrev SymM := StateRefT State MetaM

def SymM.run (x : SymM α) : MetaM α := do
  let debug := sym.debug.get (← getOptions)
  x |>.run' { debug }

/--
Applies hash-consing to `e`. Recall that all expressions in a `grind` goal have
been hash-consed. We perform this step before we internalize expressions.
-/
def shareCommon (e : Expr) : SymM Expr := do
  let share ← modifyGet fun s => (s.share, { s with share := {} })
  let (e, share) := shareCommonAlpha e share
  modify fun s => { s with share }
  return e

/--
Incremental variant of `shareCommon` for expressions constructed from already-shared subterms.

Use this when an expression `e` was produced by a Lean API (e.g., `inferType`, `mkApp4`) that
does not preserve maximal sharing, but the inputs to that API were already maximally shared.

Unlike `shareCommon`, this function does not use a local `Std.HashMap ExprPtr Expr` to
track visited nodes. This is more efficient when the number of new (unshared) nodes is small,
which is the common case when wrapping API calls that build a few constructor nodes around
shared inputs.

Example:
```
-- `a` and `b` are already maximally shared
let result := mkApp2 f a b  -- result is not maximally shared
let result ← shareCommonInc result -- efficiently restore sharing
```
-/
def shareCommonInc (e : Expr) : SymM Expr := do
  let share ← modifyGet fun s => (s.share, { s with share := {} })
  let (e, share) := shareCommonAlphaInc e share
  modify fun s => { s with share }
  return e

@[inherit_doc shareCommonInc]
abbrev share (e : Expr) : SymM Expr :=
  shareCommonInc e

/-- Returns `true` if `sym.debug` is set -/
@[inline] def isDebugEnabled : SymM Bool :=
  return (← get).debug

end Lean.Meta.Sym
