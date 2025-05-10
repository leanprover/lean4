/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Simp

namespace Lean.Meta.Grind

/--
If `e` has not been internalized yet, instantiate metavariables, unfold reducible, canonicalize,
and internalize the result.

This is an auxliary function used at `proveEq?` and `proveHEq?`.
-/
private def ensureInternalized (e : Expr) : GoalM Expr := do
  if (← alreadyInternalized e) then
    return e
  else
    /-
    It is important to expand reducible declarations. Otherwise, we cannot prove
    `¬ a = []` and `b ≠ []` by congruence closure even when `a` and `b` are in the same
    equivalence class.
    -/
    let e ← shareCommon (← canon (← unfoldReducible (← instantiateMVars e)))
    internalize e 0
    return e

private structure AbstractM.Context where
  offset : Nat := 0

private structure AbstractM.State where
  cache       : Std.HashMap (Expr × Expr) Expr := {}
  varTypes    : Array Expr  := #[]
  lhss        : Array Expr  := #[]
  rhss        : Array Expr  := #[]

private abbrev AbstractM := ReaderT AbstractM.Context $ StateT AbstractM.State $ OptionT GoalM

private def inBinder : AbstractM Bool :=
  return (← read).offset > 0

private abbrev withIncOffset (x : AbstractM α) : AbstractM α :=
  withReader (fun ctx => { ctx with offset := ctx.offset + 1 }) x

private def mkLambdaWithBodyAndVarType (varTypes : Array Expr) (b : Expr) : Expr := Id.run do
  let mut i := 0
  let mut f := b
  for varType in varTypes do
    f := mkLambda ((`_x).appendIndexAfter i) .default varType f
  return f

private partial def abstractGroundMismatches? (lhs rhs : Expr) : GoalM (Option (Expr × Expr)) := do
  let lhs ← shareCommon lhs
  let rhs ← shareCommon rhs
  let some (f, s) ← go lhs rhs |>.run {} |>.run {} |>.run
    | return none
  let f := mkLambdaWithBodyAndVarType s.varTypes f
  return some (mkAppN f s.lhss, mkAppN f s.rhss)
where
  goCore (lhs rhs : Expr) : AbstractM Expr := do
    if (← inBinder) then
      if !lhs.hasLooseBVars && !rhs.hasLooseBVars then
        let lhs ← ensureInternalized lhs
        let rhs ← ensureInternalized rhs
        processNewFacts
        trace[grind.debug.proveEq] "isEqv ({← isEqv lhs rhs}): ({lhs}) = ({rhs})"
        if (← isEqv lhs rhs) then
        if (← hasSameType lhs rhs) then
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
    trace[grind.debug.proveEq] "go: ({lhs}) = ({rhs})"
    if isSameExpr lhs rhs then
      return lhs
    if let some e := (← get).cache[(lhs, rhs)]? then
      return e
    let r ← goCore lhs rhs
    modify fun s => { s with cache := s.cache.insert (lhs, rhs) r }
    return r

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
    let lhs ← ensureInternalized lhs
    let rhs ← ensureInternalized rhs
    processNewFacts
    if (← isEqv lhs rhs) then
      return some (← mkEqProof lhs rhs)
    else if abstract then
      tryAbstract lhs rhs
    else
      return none
where
  tryAbstract (lhs₀ rhs₀ : Expr) : GoalM (Option Expr) := do
    let some (lhs, rhs) ← abstractGroundMismatches? lhs₀ rhs₀ | return none
    trace[grind.debug.proveEq] "abstract: ({lhs}) = ({rhs})"
    let lhs ← ensureInternalized lhs
    let rhs ← ensureInternalized rhs
    processNewFacts
    if (← isEqv lhs rhs) then
      return some (← mkEqProof lhs rhs)
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
    let lhs ← ensureInternalized lhs
    let rhs ← ensureInternalized rhs
    processNewFacts
    unless (← isEqv lhs rhs) do return none
    mkHEqProof lhs rhs

end Lean.Meta.Grind
