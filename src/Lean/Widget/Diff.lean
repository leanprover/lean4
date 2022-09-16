/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: E.W.Ayers
-/
import Lean.Meta.PPGoal
import Lean.Widget.InteractiveCode
import Lean.Widget.InteractiveGoal
import Lean.Data.Lsp.Extra

namespace Lean.Widget

open Server Std Lean SubExpr

open Lean.Expr in
/-- Define `m₁` to be the parent of `m₂` in a given mvar-context when `m₁` has been
assigned with an expression containing `m₂`.

Some technicalities:
Suppose `m₁ : (n : Nat) → P`, and the new goal `n : Nat ⊢ m₂ : P` was got with an application of `intro`.
Now, `m₁` is assigned the expression `fun (n : Nat) => m₃ n`.
`m₃` is an auxilliary mvar with a delayed assignment, so we have to look a step further if there is a delayed mvar.

-/
partial def isParent (m₁ m₂ : MVarId): MetaM Bool := core m₁ 2
  where core (m₁ : MVarId) (fuel : Nat) : MetaM Bool := do
    let some assignment ← Lean.getExprMVarAssignment? m₁ | return false
    let assignment ← instantiateMVars assignment
    let r ← assignment.findExtM? (fun e => do
      if !e.hasMVar then return FindStep.done else
      match e with
      | .mvar m =>
        if m == m₂ then
          return FindStep.found
        let m' ← getDelayedMVarRoot m
        if m' == m₂ then
          return FindStep.found
        if m' != m ∧ (← m'.isAssigned) ∧ fuel > 0 then
          if ← core m' (fuel - 1) then -- [todo] is this wf without fuel?
            return FindStep.found
        return FindStep.done
      | _ => return FindStep.visit
    )
    return r.isSome

/-- A marker for a point in the expression where a subexpression has been inserted.

NOTE: in the future we may add other tags such as `deleted` or `end_insert`.
  -/
inductive ExprDiffPoint where
  | inserted

def ExprDiffPoint.toString : ExprDiffPoint → String
  | .inserted => "inserted"

def ExprDiffPoint.fromString : String → Except String ExprDiffPoint
  | "inserted" => Except.ok ExprDiffPoint.inserted
  | s => Except.error s!"expected an ExprDiffPoint ctor string but got {s}"

instance : FromJson ExprDiffPoint where
  fromJson? j := j.getStr? >>= ExprDiffPoint.fromString

instance : ToJson ExprDiffPoint where
  toJson x := x.toString |> Json.str

/-- A description of the differences between a pair of expressions `e₀`, `e₁`.
The information is only used to display a 'visual diff' for `e₁`. -/
structure ExprDiff where
  /-- A map from subexpr positions in `e₁` to 'diff points' which are tags
  describing how the expression is changed at the given position.-/
  changes : PosMap ExprDiffPoint := ∅

instance : EmptyCollection ExprDiff := ⟨{}⟩
instance : Append ExprDiff where
  append a b := {changes := RBMap.mergeBy (fun _ _ b => b) a.changes b.changes}

/-- Creates an ExprDiff with a single diff point. -/
def ExprDiff.singleton (p : Pos) (d : ExprDiffPoint) : ExprDiff :=
  RBMap.empty |>.insert p d |> ExprDiff.mk

/-- If true, the expression before and the expression after are identical. -/
def ExprDiff.isEmpty (d : ExprDiff) : Bool :=
  RBMap.isEmpty <| d.changes

/-- Determines whether the given expressions have the same function head and
the same number of arguments. -/
def sameHead (e₀ e₁ : Expr) : MetaM Bool := do
  if e₀ == e₁ then return true
  let f₀ := e₀.getAppFn
  let f₁ := e₁.getAppFn
  if f₀ != f₁ then
    return false
  return e₀.getAppNumArgs == e₁.getAppNumArgs

/-- Returns true if the expressions are completely different. -/
def ExprDiff.isRootReplacement (d : ExprDiff) : MetaM Bool := do
  if d.isEmpty then return false else
  match d.changes.find? Pos.root with
  | (some .inserted) => return true
  | _ => return false

/-- Computes a diff between `before` and `after` expressions.

This works by recursively comparing function arguments.

TODO(ed):
- diffs under binders, particularly if the binder count has changed as after `intro`.
- experiment with a 'greatest common subexpression' design where
  given `e₀`, `e₁`, find the greatest common subexpressions `Xs : Array Expr` and a congruence `F` such that
  `e₀ = F[A₀[..Xs]]` and `e₀ = F[A₁[..Xs]]`. Then, we can have fancy diff highlighting where common subexpressions are not highlighted.
 -/
partial def exprDiff (before after : Expr) (p : Pos := Pos.root) : MetaM ExprDiff := do
  if before == after then
    return ∅
  if !(← sameHead before after) then
    return ExprDiff.singleton p ExprDiffPoint.inserted
  let afterArgs := after.getAppArgs
  let beforeArgs := before.getAppArgs
  if afterArgs.size == 0 then
    return ExprDiff.singleton p ExprDiffPoint.inserted
  let n := afterArgs.size
  let bas := Array.zip beforeArgs afterArgs
  let numDifferent := bas.filter (fun (a,b) => a != b) |>.size
  if numDifferent > 1 ∧ p != Pos.root then
    /- heuristic: if we are not at the root expression and more than one
     argument is different, we say that the change has occurred at the head term.
     eg if comm `x + y ↝ y + x`, we want to highlight all of `y + x`.
     One common case is if `⊢ A = B` and a tactic rewrites both `A` and `B`.
     in this case it looks a little better to recurse the diff to `A` and `B` separately.
    -/
    return ExprDiff.singleton p ExprDiffPoint.inserted
  let rs : Array ExprDiff ← bas.mapIdxM (fun i (x,y) => do
    exprDiff x y <| p.pushNaryArg n i
  )
  return rs.foldl (init := ∅) (· ++ ·)

/-- Given a `diff` between `before` and `after : Expr`, and the rendered `infoAfter : CodeWithInfos` for `after`,
this function decorates `infoAfter` with tags indicating where the expression has changed. -/
def addDiffTags (diff : ExprDiff) (infoAfter : CodeWithInfos) : MetaM CodeWithInfos := do
  if diff.isEmpty then
    return infoAfter
  let tt ← infoAfter.mapM (fun (info : SubexprInfo) => do
    if let some d := diff.changes.find? info.subexprPos then
      return info.appendTag <| d.toString
    else
      return info
  )
  return tt

open Meta

def diffHypothesesBundle (ctx₀  : LocalContext) (h₁ : InteractiveHypothesisBundle) : MetaM InteractiveHypothesisBundle := do
  /- Strategy: we say a hypothesis has mutated if the ppName is the same but the fvarid has changed.
     this indicates that something like `rewrite at` has hit it. -/
  for (ppName, fvid) in Array.zip h₁.names h₁.fvarIds do
    if !(ctx₀.contains fvid) then
      if let some decl₀ := ctx₀.findFromUserName? ppName then
        -- on the old context there was an fvar with the same name as this one.
        let t₀ := decl₀.type
        try
          return ← withTypeDiff t₀ h₁
        catch e =>
          let f ← e.toMessageData.format
          return {h₁ with message? := s!"{f}"}
      else
        return {h₁ with isInserted? := true}
  -- all fvids are present on original so we can assume no change.
  return h₁
  where withTypeDiff (t₀ : Expr) (h₁ : InteractiveHypothesisBundle) : MetaM InteractiveHypothesisBundle := do
      let some x₁ := h₁.fvarIds[0]?
        | return {h₁ with message? := "internal error: empty fvar list!"}
      let t₁ ← inferType <| Expr.fvar x₁
      let tδ ← exprDiff t₀ t₁
      let c₁ ← addDiffTags tδ h₁.type
      return {h₁ with type := c₁}

def diffHypotheses (lctx₀ : LocalContext) (hs₁ : Array InteractiveHypothesisBundle) : MetaM (Array InteractiveHypothesisBundle) := do
  -- [todo] also show when hypotheses (user-names present in lctx₀ but not in hs₁) are deleted
  hs₁.mapM (diffHypothesesBundle lctx₀)

def diffInteractiveGoal (g₀ : MVarId) (i₁ : InteractiveGoal) : MetaM InteractiveGoal := do
  let mut i₁ := i₁
  let mctx ← getMCtx
  let some md₀ := mctx.findDecl? g₀
    | throwError "Failed to find decl for {g₀}."
  let lctx₀ := md₀.lctx |>.sanitizeNames.run' {options := (← getOptions)}
  let hs₁ ← diffHypotheses lctx₀ i₁.hyps
  i₁ := {i₁ with hyps := hs₁}
  let some g₁ := i₁.mvarId?
    | throwError "Expected InteractiveGoal to have an mvarId"
  let some a₀  ← getExprMVarAssignment? g₀
    | throwError "Expected {g₀} to be assigned."
  let t₀ ← instantiateMVars <|← inferType a₀
  let some md₁ := (← getMCtx).findDecl? g₁
    | throwError "Unknown goal {g₁}"
  let t₁ ← instantiateMVars md₁.type
  let tδ ← exprDiff t₀ t₁
  let c₁ ← addDiffTags tδ i₁.type
  i₁ := {i₁ with type := c₁, isInserted? := false}
  return i₁

def ppMvar (m : MVarId) : MetaM Format := Meta.ppExpr <| .mvar m

/-- Modifies `goalsAfter` with additional information about how it is different to `goalsBefore`.  -/
def diffInteractiveGoals (goalsBefore : Array MVarId) (goalsAfter : InteractiveGoals) : MetaM InteractiveGoals := do
  let goals ← goalsAfter.goals.mapM (fun ig₁ => do
    let some g₁ := ig₁.mvarId?
      | return {ig₁ with message? := "error: goal not found"}
    withGoalCtx (g₁ : MVarId) (fun _lctx₁ _md₁ => do
      -- if the goal is present on the previous version then continue
      if goalsBefore.any (fun g₀ => g₀ == g₁) then
        return {ig₁ with isInserted? := none}
      let some g₀ ← goalsBefore.findM? (fun g₀ => isParent g₀ g₁)
        | return {ig₁ with
          isInserted? := true
        }
      let ig₁ ← diffInteractiveGoal g₀ ig₁
      return ig₁
    )
  )
  return {goalsAfter with goals := goals}

end Lean.Widget
