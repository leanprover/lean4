/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: E.W.Ayers
-/
module

prelude
public import Lean.Widget.InteractiveGoal

namespace Lean.Widget

register_builtin_option showTacticDiff : Bool := {
  defValue := true
  descr := "When true, interactive goals for tactics will be decorated with diffing information. "
}

open Server Std Lean SubExpr

/-- A marker for a point in the expression where a subexpression has been inserted.

NOTE: in the future we may add other tags.
  -/
inductive ExprDiffTag where
  | change
  | delete
  | insert

def ExprDiffTag.toDiffTag : (useAfter : Bool) → ExprDiffTag → Lean.Widget.DiffTag
  | true,  .change => .wasChanged
  | false, .change => .willChange
  | true,  .delete => .wasDeleted
  | false, .delete => .willDelete
  | true,  .insert => .wasInserted
  | false, .insert => .willInsert

def ExprDiffTag.toString : ExprDiffTag → String
  | .change => "change"
  | .delete => "delete"
  | .insert => "insert"

instance : ToString ExprDiffTag := ⟨ExprDiffTag.toString⟩

/-- A description of the differences between a pair of expressions `before`, `after : Expr`.
The information can be used to display a 'visual diff' for
either `before`, showing the parts of the expression that are about to change,
or `after` showing which parts of the expression have changed. -/
structure ExprDiff where
  /-- Map from subexpr positions in `e₀` to diff points.-/
  changesBefore : PosMap ExprDiffTag := ∅
  /-- A map from subexpr positions in `e₁` to 'diff points' which are tags
  describing how the expression has changed relative to `before` at the given position.-/
  changesAfter : PosMap ExprDiffTag := ∅

instance : EmptyCollection ExprDiff := ⟨{}⟩
instance : Append ExprDiff where
  append a b := {
    changesBefore := Std.TreeMap.mergeWith (fun _ _ b => b) a.changesBefore b.changesBefore,
    changesAfter := Std.TreeMap.mergeWith (fun _ _ b => b) a.changesAfter b.changesAfter
  }
instance : ToString ExprDiff where
  toString x :=
    let f := fun (p : PosMap ExprDiffTag) =>
      p.toList.map (fun (k,v) => s!"({toString k}:{toString v})")
    s!"before: {f x.changesBefore}\nafter: {f x.changesAfter}"

/-- Add a tag at the given position to the `changesBefore` dict. -/
def ExprDiff.insertBeforeChange (p : Pos) (d : ExprDiffTag := .change) (δ : ExprDiff) : ExprDiff :=
  {δ with changesBefore := δ.changesBefore.insert p d}

/-- Add a tag at the given position to the `changesAfter` dict. -/
def ExprDiff.insertAfterChange (p : Pos) (d : ExprDiffTag := .change) (δ : ExprDiff) : ExprDiff :=
  {δ with changesAfter := δ.changesAfter.insert p d}

def ExprDiff.withChangePos (before after : Pos) (d : ExprDiffTag := .change) : ExprDiff :=
  { changesAfter := Std.TreeMap.empty.insert after d
    changesBefore := Std.TreeMap.empty.insert before d
  }

/-- Add a tag to the diff at the positions given by `before` and `after`. -/
def ExprDiff.withChange (before after : SubExpr) (d : ExprDiffTag := .change) : ExprDiff :=
  ExprDiff.withChangePos before.pos after.pos d

/-- If true, the expression before and the expression after are identical. -/
def ExprDiff.isEmpty (d : ExprDiff) : Bool :=
  d.changesAfter.isEmpty ∧ d.changesBefore.isEmpty

/-- Computes a diff between `before` and `after` expressions.

This works by recursively comparing function arguments.

TODO(ed): experiment with a 'greatest common subexpression' design where
  given `e₀`, `e₁`, find the greatest common subexpressions `Xs : Array Expr` and a congruence `F` such that
  `e₀ = F[A₀[..Xs]]` and `e₀ = F[A₁[..Xs]]`. Then, we can have fancy diff highlighting where common subexpressions are not highlighted.

## Diffing binders

Two binding domains are identified if they have the same user name and the same type.
The most common tactic that modifies binders is after an `intros`.
To deal with this case, if `before = (a : α) → β` and `after`, is not a matching binder (ie: not `(a : α) → _`)
then we instantiate the `before` variable in a new context and continue diffing `β` against `after`.

 -/
partial def exprDiffCore (before after : SubExpr) : MetaM ExprDiff := do
  if before.expr == after.expr then
    return ∅
  match before.expr, after.expr with
  | .mdata _ e₀, _ => exprDiffCore {before with expr := e₀} after
  | _, .mdata _ e₁ => exprDiffCore before {after with expr := e₁}
  | .app .., .app .. =>
    let (fn₀, args₀) := after.expr.withApp Prod.mk
    let (fn₁, args₁) := before.expr.withApp Prod.mk
    if fn₀ != fn₁ || args₀.size != args₁.size then
      return ExprDiff.withChange before after
    let args := Array.zip args₀ args₁
    let args ← args.mapIdxM (fun i (beforeArg, afterArg) =>
      exprDiffCore
        ⟨beforeArg, before.pos.pushNaryArg args₀.size i⟩
        ⟨afterArg,  after.pos.pushNaryArg  args₀.size i⟩
    )
    return args.foldl (init := ∅) (· ++ ·)
  | .forallE .., _ => piDiff before after
  | .lam n₀ d₀ b₀ i₀, .lam n₁ d₁ b₁ i₁=>
    if n₀ != n₁ || i₀ != i₁ then
      return ExprDiff.withChange before after
    let δd ← exprDiffCore ⟨d₀, before.pos.pushBindingDomain⟩ ⟨d₁, after.pos.pushBindingDomain⟩
    if δd.isEmpty then
      return ← exprDiffCore ⟨b₀, before.pos.pushBindingBody⟩ ⟨b₁, after.pos.pushBindingBody⟩
    else
      return δd ++ ExprDiff.withChangePos before.pos.pushBindingBody after.pos.pushBindingBody
  | .proj n₀ i₀ e₀, .proj n₁ i₁ e₁ =>
    if n₀ != n₁ || i₀ != i₁ then
      return ExprDiff.withChange before after
    else
      exprDiffCore ⟨e₀, before.pos.pushProj⟩ ⟨e₁, after.pos.pushProj⟩
  | _, _ => return ExprDiff.withChange before after
  where
    piDiff (before after : SubExpr) : MetaM ExprDiff := do
      let .forallE n₀ d₀ b₀ i₀ := before.expr
        | return ∅
      if let .forallE n₁ d₁ b₁ i₁ := after.expr then
        if n₀ == n₁ && i₀ == i₁ then
          -- assume that these are the same binders
          let δd ← exprDiffCore
            ⟨d₀, before.pos.pushBindingDomain⟩
            ⟨d₁, after.pos.pushBindingDomain⟩
          if δd.isEmpty then
            -- the types have changed, so we can no longer meaningfully compare the targets
            let δt ← Lean.Meta.withLocalDecl n₀ i₀ d₀ fun x =>
              exprDiffCore
                ⟨b₀.instantiate1 x, before.pos.pushBindingBody⟩
                ⟨b₁.instantiate1 x, after.pos.pushBindingBody⟩
            return δt
          else
            return δd ++ ExprDiff.withChangePos before.pos.pushBindingBody after.pos.pushBindingBody
      -- in this case, the after expression does not match the before expression.
      -- however, a special case is intros:
      if let some s := List.isSuffixOf? after.expr.getForallBinderNames before.expr.getForallBinderNames then
        -- s ++ namesAfter = namesBefore
        if s.length == 0 then
          throwError "should not happen"
        let body₀ := before.expr.getForallBodyMaxDepth s.length
        let mut δ : ExprDiff ← (do
          -- this line can fail if we are using `before`'s mvar context, in which case
          -- we can skip giving a diff.
          let fvars ← s.mapM Lean.Meta.getFVarFromUserName
          return ← exprDiffCore
            ⟨body₀.instantiateRev fvars.toArray, before.pos.pushNthBindingBody s.length⟩
            after
        ) <|> (pure ∅)
        for i in *...s.length do
          δ := δ.insertBeforeChange (before.pos.pushNthBindingDomain i) .delete
        -- [todo] maybe here insert a tag on the after case indicating an expression was deleted above the expression?
        return δ
      return ExprDiff.withChange before after

/-- Computes the diff for `e₀` and `e₁`. If `useAfter` is `false`, `e₀, e₁` are interpreted as `after, before` instead of `before, after`.-/
def exprDiff (e₀ e₁ : Expr) (useAfter := true) : MetaM ExprDiff := do
  let s₀ := ⟨e₀, Pos.root⟩
  let s₁ := ⟨e₁, Pos.root⟩
  if useAfter then
    exprDiffCore s₀ s₁
  else
    exprDiffCore s₁ s₀

/-- Given a `diff` between `before` and `after : Expr`, and the rendered `infoAfter : CodeWithInfos` for `after`,
this function decorates `infoAfter` with tags indicating where the expression has changed.

If `useAfter == false` before and after are swapped. -/
def addDiffTags (useAfter : Bool) (diff : ExprDiff) (info₁ : CodeWithInfos) : MetaM CodeWithInfos := do
  let cs := if useAfter then diff.changesAfter else diff.changesBefore
  info₁.mergePosMap (fun info d => pure <| info.withDiffTag <| ExprDiffTag.toDiffTag useAfter d) cs

open Meta

/-- Diffs the given hypothesis bundle against the given local context.

If `useAfter == true`, `ctx₀` is the context _before_ and `h₁` is the bundle _after_.
If `useAfter == false`, these are swapped.
 -/
def diffHypothesesBundle (useAfter : Bool) (ctx₀  : LocalContext) (h₁ : InteractiveHypothesisBundle) : MetaM InteractiveHypothesisBundle := do
  /- Strategy: we say a hypothesis has mutated if the ppName is the same but the fvarid has changed.
     this indicates that something like `rewrite at` has hit it. -/
  for (ppName, fvid) in Array.zip h₁.names h₁.fvarIds do
    if !(ctx₀.contains fvid) then
      if let some decl₀ := ctx₀.findFromUserName? (.mkSimple ppName) then
        -- on ctx₀ there is an fvar with the same name as this one.
        let t₀ ← instantiateMVars decl₀.type
        return ← withTypeDiff t₀ h₁
      else
        if useAfter then
          return {h₁ with isInserted? := true }
        else
          return {h₁ with isRemoved? := true }
  -- all fvids are present on original so we can assume no change.
  return h₁
where
  withTypeDiff (t₀ : Expr) (h₁ : InteractiveHypothesisBundle) : MetaM InteractiveHypothesisBundle := do
    let some x₁ := h₁.fvarIds[0]?
      | throwError "internal error: empty fvar list!"
    let t₁ ← instantiateMVars =<< inferType (Expr.fvar x₁)
    let tδ ← exprDiff t₀ t₁ useAfter
    let c₁ ← addDiffTags useAfter tδ h₁.type
    return {h₁ with type := c₁}

def diffHypotheses (useAfter : Bool) (lctx₀ : LocalContext) (hs₁ : Array InteractiveHypothesisBundle) : MetaM (Array InteractiveHypothesisBundle) := do
  -- [todo] also show when hypotheses (user-names present in lctx₀ but not in hs₁) are deleted
  hs₁.mapM (diffHypothesesBundle useAfter lctx₀)

/-- Decorates the given goal `i₁` with a diff by comparing with goal `g₀`.
If `useAfter` is true then `i₁` is _after_ and `g₀` is _before_. Otherwise they are swapped. -/
def diffInteractiveGoal (useAfter : Bool) (g₀ : MVarId) (i₁ : InteractiveGoal) : MetaM InteractiveGoal := do
  let mctx ← getMCtx
  let some md₀ := mctx.findDecl? g₀
    | throwError "Failed to find decl for {g₀}."
  let lctx₀ := md₀.lctx |>.sanitizeNames.run' {options := (← getOptions)}
  let hs₁ ← diffHypotheses useAfter lctx₀ i₁.hyps
  let i₁ := {i₁ with hyps := hs₁}
  let g₁ := i₁.mvarId
  let t₀ ← instantiateMVars <|← inferType (Expr.mvar g₀)
  let some md₁ := (← getMCtx).findDecl? g₁
    | throwError "Unknown goal {g₁}"
  let t₁ ← instantiateMVars md₁.type
  let tδ ← exprDiff t₀ t₁ useAfter
  let c₁ ← addDiffTags useAfter tδ i₁.type
  let i₁ := {i₁ with type := c₁, isInserted? := false}
  return i₁

/-- Modifies `goalsAfter` with additional information about how it is different to `goalsBefore`.
If `useAfter` is `true` then `igs₁` is the set of interactive goals _after_ the tactic has been applied.
Otherwise `igs₁` is the set of interactive goals _before_. -/
public def diffInteractiveGoals (useAfter : Bool) (info : Elab.TacticInfo) (igs₁ : InteractiveGoals) : MetaM InteractiveGoals := do
    if ! showTacticDiff.get (← getOptions) then return igs₁ else
    let goals₀ := if useAfter then info.goalsBefore else info.goalsAfter
    let parentMap : MVarIdMap MVarIdSet ← info.goalsBefore.foldlM (init := ∅) (fun s g => do
      let ms ← Expr.mvar g |> Lean.Meta.getMVars
      let ms := MVarIdSet.ofArray ms
      return s.insert g ms
    )
    let isParent (before after : MVarId) : Bool :=
       match parentMap.get? before with
       | some xs => xs.contains after
       | none => false
    let goals ← igs₁.goals.mapM (fun ig₁ => do
      let g₁ := ig₁.mvarId
      withGoalCtx (g₁ : MVarId) (fun _lctx₁ _md₁ => do
        -- if the goal is present on the previous version then continue
        if goals₀.any (fun g₀ => g₀ == g₁) then
          return {ig₁ with isInserted? := none}
        let some g₀ := goals₀.find? (fun g₀ => if useAfter then isParent g₀ g₁ else isParent g₁ g₀)
          | return if useAfter then {ig₁ with isInserted? := true } else {ig₁ with isRemoved? := true}
        let ig₁ ← diffInteractiveGoal useAfter g₀ ig₁
        return ig₁
      )
    )
    return {igs₁ with goals := goals}

end Lean.Widget
