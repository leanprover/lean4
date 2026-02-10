/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Simp
public section
namespace Lean.Meta.Grind
/--
If `e` has not been internalized yet, instantiate metavariables, unfold reducible, canonicalize,
and internalize the result.

This is an auxiliary function used at `proveEq?` and `proveHEq?`.
-/
private def ensureInternalized (e : Expr) : GoalM Simp.Result := do
  if (← alreadyInternalized e) then
    return { expr := e }
  else
    /-
    It is important to expand reducible declarations. Otherwise, we cannot prove
    `¬ a = []` and `b ≠ []` by congruence closure even when `a` and `b` are in the same
    equivalence class.
    -/
    preprocessAndInternalize (← instantiateMVars e) 0

/-!
`abstractGroundMismatches?` is an auxiliary function for creating auxiliary equality
proofs. When trying to prove `lhs = rhs`, we use two different approaches. In the first
one, we just internalize the terms, propagate, and then check whether they are in the same
equivalence class. The function `abstractGroundMismatches?` is used to implement the
second approach that focus on terms containing binders. Here is a motivating example,
suppose we are trying to prove that `(b : Bool) → a[i]? = some b → Nat` is equal to
`(b : Bool) → some v = some b → Nat` and the goal contains the equivalence class
`{a[i]?, some v}`.
Congruence closure does not process terms containing free variables, and fails to
prove the equality.
`abstractGroundMismatches?` extracts ground terms that are equal in the current goal,
and creates an auxiliary function. In the example above, the following two terms
are generated.
- `(fun x => (b : Bool) → x = some b → Nat) a[i]?`
- `(fun x => (b : Bool) → x = some b → Nat) (some v)`

The two new terms are definitionally equal to the original ones, but congruence
closure will now detect the equality.

The motivation for this infrastructure is match-expression equalities.
Suppose we have
```
match h : assign[v]? with
| none => ...
| some b => ...
```
When instantiating the match-expr equations for the `none` and `some` cases,
we need to introduce casts.
-/

/-- Context for the `AbstractM` monad used to implement `abstractGroundMismatches?` -/
private structure AbstractM.Context where
  /-- Number of binders under which the terms being processed occur under. -/
  offset : Nat := 0

/-- State for the `AbstractM` monad used to implement `abstractGroundMismatches?` -/
private structure AbstractM.State where
  cache       : Std.HashMap (Expr × Expr) Expr := {}
  /-- Types of the new variables created for the auxiliary `fun`. -/
  varTypes    : Array Expr  := #[]
  /-- Ground terms from the `lhs` that have been abstracted so far. -/
  lhss        : Array Expr  := #[]
  /-- Ground terms from the `rhs` that have been abstracted so far. -/
  rhss        : Array Expr  := #[]

/-- Helper monad for implementing `abstractGroundMismatches?` -/
private abbrev AbstractM := ReaderT AbstractM.Context $ StateT AbstractM.State $ OptionT GoalM

/-- Returns `true` if current terms occur under binders. -/
private def inBinder : AbstractM Bool :=
  return (← read).offset > 0

/-- Executes `x` in a context where the number of binders have been increased. -/
private abbrev withIncOffset (x : AbstractM α) : AbstractM α :=
  withReader (fun ctx => { ctx with offset := ctx.offset + 1 }) x

/--
Returns `fun (x_0 : varTypes[0]) ... (x_n : varTypes[n]) => b`.
`b` contains `varTypes.size` loose bound variables.
-/
private def mkLambdaWithBodyAndVarType (varTypes : Array Expr) (b : Expr) : Expr := Id.run do
  let mut i := 0
  let mut f := b
  for varType in varTypes do
    f := mkLambda ((`_x).appendIndexAfter i) .default varType f
  return f

/--
Helper function for `proveEq?`. It abstracts nested ground terms in `lhs` and `rhs`.
Suppose `lhs` is `(b : Bool) → a[i]? = some b → Nat`, and
`rhs` is `(b : Bool) → some v = some b → Nat`.
Then, the result is
- `(fun x => (b : Bool) → x = some b → Nat) a[i]?`
- `(fun x => (b : Bool) → x = some b → Nat) (some v)`
-/
private partial def abstractGroundMismatches? (lhs rhs : Expr) : GoalM (Option (Expr × Expr)) := do
  let lhs ← shareCommon lhs
  let rhs ← shareCommon rhs
  let some (f, s) ← go lhs rhs |>.run {} |>.run {} |>.run
    | return none
  if s.lhss.isEmpty then
    return none
  let f := mkLambdaWithBodyAndVarType s.varTypes f
  return some (mkAppN f s.lhss, mkAppN f s.rhss)
where
  goCore (lhs rhs : Expr) : AbstractM Expr := do
    if (← inBinder) then
      if !lhs.hasLooseBVars && !rhs.hasLooseBVars then
        let rl ← ensureInternalized lhs
        let rr ← ensureInternalized rhs
        processNewFacts
        if (← isEqv rl.expr rr.expr) then
        if (← hasSameType rl.expr rr.expr) then
        let varType ← inferType lhs
        let varIdx := (← get).varTypes.size + (← read).offset
        modify fun s => { s with
          varTypes := s.varTypes.push varType
          lhss := s.lhss.push lhs
          rhss := s.rhss.push rhs
        }
        return mkBVar varIdx
    match lhs with
    | .lit _ | .sort _ | .mvar _ | .fvar _
    | .bvar _ | .const .. => failure
    | .mdata d₁ b₁ =>
      let .mdata _ b₂ := rhs | failure
      return .mdata d₁ (← go b₁ b₂)
    | .proj n₁ i₁ b₁ =>
      let .proj n₂ i₂ b₂ := rhs | failure
      guard (n₁ == n₂ && i₁ == i₂)
      return .proj n₁ i₁ (← go b₁ b₂)
    | .app f₁ a₁ =>
      let .app f₂ a₂ := rhs | failure
      return mkApp (← go f₁ f₂) (← go a₁ a₂)
    | .forallE n₁ d₁ b₁ i₁ =>
      let .forallE _ d₂ b₂ _ := rhs | failure
      return mkForall n₁ i₁ (← go d₁ d₂) (← withIncOffset <| go b₁ b₂)
    | .lam n₁ d₁ b₁ i₁  =>
      let .lam _ d₂ b₂ _ := rhs | failure
      return mkLambda n₁ i₁ (← go d₁ d₂) (← withIncOffset <| go b₁ b₂)
    | .letE n₁ t₁ v₁ b₁ nd₁ =>
      let .letE _ t₂ v₂ b₂ _ := rhs | failure
      return mkLet n₁ (← go t₁ t₂) (← go v₁ v₂) (← withIncOffset <| go b₁ b₂) nd₁

  go (lhs rhs : Expr) : AbstractM Expr := do
    if isSameExpr lhs rhs then
      return lhs
    if let some e := (← get).cache[(lhs, rhs)]? then
      return e
    let r ← goCore lhs rhs
    modify fun s => { s with cache := s.cache.insert (lhs, rhs) r }
    return r

/-!
Helper functions for creating equalities proofs.
-/

/--
Try to construct a proof that `lhs = rhs` using the information in the
goal state. If `lhs` and `rhs` have not been internalized, this function
will internalize then, process propagated equalities, and then check
whether they are in the same equivalence class or not.
The goal state is not modified by this function.
This function mainly relies on congruence closure, and constraint
propagation. It will not perform case analysis.
-/
def proveEq? (lhs rhs : Expr) (abstract : Bool := false) : GoalM (Option Expr) := do
  trace[grind.debug.proveEq] "({lhs}) = ({rhs})"
  unless (← hasSameType lhs rhs) do return none
  if (← alreadyInternalized lhs <&&> alreadyInternalized rhs) then
    if (← isEqv lhs rhs) then
      return some (← mkEqProof lhs rhs)
    else if abstract then withoutModifyingState do
      tryAbstract lhs rhs
    else
      return none
  else withoutModifyingState do
    /-
    We used to apply the `grind` normalizer, but it created unexpected failures.
    Here is an example, suppose we are trying to prove `i < (a :: l).length` is equal to `0 < (a :: l).length`
    when `i` and `0`  are in the same equivalence class. This should hold by applying congruence closure.
    However, if we apply the normalizer, we obtain `i+1 ≤ (a :: l).length` and `1 ≤ (a :: l).length`, and
    the equality cannot be detected by congruence closure anymore.
    -/
    let rl ← ensureInternalized lhs
    let rr ← ensureInternalized rhs
    processNewFacts
    if (← isEqv rl.expr rr.expr) then
      return some (← composeEqProof rl rr)
    else if abstract then
      tryAbstract lhs rhs
    else
      return none
where
  /-- Compose preprocessing proofs with the E-graph equality proof. -/
  composeEqProof (rl rr : Simp.Result) : GoalM Expr := do
    let mut proof ← mkEqProof rl.expr rr.expr
    if let some hp := rl.proof? then
      proof ← mkEqTrans hp proof
    if let some hp := rr.proof? then
      proof ← mkEqTrans proof (← mkEqSymm hp)
    return proof
  tryAbstract (lhs₀ rhs₀ : Expr) : GoalM (Option Expr) := do
    let some (lhs, rhs) ← abstractGroundMismatches? lhs₀ rhs₀ | return none
    trace[grind.debug.proveEq] "abstract: ({lhs}) = ({rhs})"
    let rl ← ensureInternalized lhs
    let rr ← ensureInternalized rhs
    processNewFacts
    if (← isEqv rl.expr rr.expr) then
      return some (← composeEqProof rl rr)
    else
      return none

/-- Similar to `proveEq?`, but for heterogeneous equality. -/
def proveHEq? (lhs rhs : Expr) : GoalM (Option Expr) := do
  if (← alreadyInternalized lhs <&&> alreadyInternalized rhs) then
    if (← isEqv lhs rhs) then
      return some (← mkHEqProof lhs rhs)
    else
      return none
  else withoutModifyingState do
    -- See comment at `proveEq?`
    let rl ← ensureInternalized lhs
    let rr ← ensureInternalized rhs
    processNewFacts
    unless (← isEqv rl.expr rr.expr) do return none
    let mut proof ← mkHEqProof rl.expr rr.expr
    if let some hp := rl.proof? then
      proof ← mkHEqTrans (← mkHEqOfEq hp) proof
    if let some hp := rr.proof? then
      proof ← mkHEqTrans proof (← mkHEqSymm (← mkHEqOfEq hp))
    return proof

end Lean.Meta.Grind
