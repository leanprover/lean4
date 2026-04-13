/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Lean.Attributes
public import Lean.Meta.Basic

/-!
# The `@[expect_true]` attribute

The `@[expect_true h₁ h₂ ...]` attribute marks hypotheses of a `simp` lemma as "expected to be
true". Normally, `simp` silently skips a conditional rewrite lemma when it cannot discharge its side
conditions. With `expect_true`, `simp` applies the rewrite anyway and leaves the undischarged
hypotheses as new goals.

## Example

```lean
@[expect_true h, simp]
theorem List.get!_toList_range {i hi : Nat} (h : i < hi) :
    (List.range hi)[i]! = i := ...

example (hi i : Nat) (h : i * i < i * hi) : (List.range hi)[i]! = i := by
  simp only [List.get!_toList_range]
  -- remaining goal: `i < hi`
  exact Nat.lt_of_mul_lt_mul_left h
```

## Behavior

- Discharge is still attempted first. If `simp`'s discharger proves an `expect_true` condition (e.g.
  via `decide` or another simp lemma), no goal is spawned.
- Goals are only created for theorems that `simp` actually applies. An `expect_true` lemma that is
  never matched produces no goals.
- When multiple `expect_true` lemmas are used, their undischarged conditions accumulate as goals in
  application order, after the main goal.

## Implementation notes

For `expect_true` theorems, the rewrite machinery in `Rewrite.lean` bypasses `withNewMCtxDepth` and
uses manual metavar-context save/restore (`withMCtxRollback`). This is necessary because
`withNewMCtxDepth` discards all metavar assignments on exit, which would destroy the pending goal
metavars. The manual approach restores the metavar context only on failure; on success the pending
metavars survive and are threaded through `Simp.State.pendingGoals` / `Simp.Stats.pendingGoals` to
the tactic layer, which appends them to the goal list.

The consequence of bypassing `withNewMCtxDepth` is that the depth-based protection against
accidental assignment of outer metavariables during unification is lost for `expect_true` theorems.
In practice `simp` operates on fully instantiated expressions, so this is benign.
-/

public section

namespace Lean.Meta.Simp

/-- Collect all binder names from a forall-telescope (without reducing). -/
private partial def collectBinderNames (type : Expr) : Array Name :=
  go type #[]
where
  go (type : Expr) (acc : Array Name) : Array Name :=
    match type with
    | .forallE n _ b _ => go b (acc.push n)
    | _ => acc

/--
The `@[expect_true h₁ h₂ ...]` attribute marks hypotheses of a `simp` lemma that are "expected to
be true". When `simp` applies the lemma but cannot discharge these hypotheses, it applies the rewrite
anyway and leaves the undischarged hypotheses as new goals for the user.

This is useful for lemmas about partial operations (like `get!`, `head!`) where bounds conditions
are typically satisfied but may not be automatically provable.
-/
builtin_initialize expectTrueAttr : ParametricAttribute (Array Name) ←
  registerParametricAttribute {
    name := `expect_true
    descr := "mark hypotheses that simp should leave as goals when it cannot discharge them"
    getParam := fun declName stx => do
      let args := stx[1].getArgs
      if args.isEmpty then
        throwError "expect_true requires at least one hypothesis name"
      let names ← args.mapM fun arg => do
        let name := arg.getId
        if name.isAnonymous then
          throwError "expect_true: invalid hypothesis name"
        return name
      let info ← getConstInfo declName
      let binderNames := collectBinderNames info.type
      for name in names do
        unless binderNames.contains name do
          throwError "expect_true: hypothesis '{name}' not found in the binders of '{declName}'"
      return names
  }

/-- Look up which hypotheses are marked `@[expect_true]` for a declaration. -/
def getExpectTrueHyps? (env : Environment) (declName : Name) : Option (Array Name) :=
  expectTrueAttr.getParam? env declName

/--
Given metavars `xs` created by `forallMetaTelescopeReducing`, determine which indices
correspond to `expect_true` hypothesis names by matching against mvar `userName`s.
-/
def getExpectTrueIndices (xs : Array Expr) (expectTrueNames : Array Name) :
    MetaM (Array Nat) := do
  let mut indices : Array Nat := #[]
  for h : i in [:xs.size] do
    let x := xs[i]
    if x.isMVar then
      let decl ← x.mvarId!.getDecl
      if expectTrueNames.contains decl.userName then
        indices := indices.push i
  return indices

end Lean.Meta.Simp
