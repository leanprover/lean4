/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.ScopedEnvExtension
public import Lean.Attributes
public import Lean.Meta.Sym.Apply
public import Lean.Meta.Sym.Simp.DiscrTree

/-!
The `@[vcgen_rintro]` attribute registers the rules by which `vcgen` destructures a binder while it
introduces the binders of the target, like an `rintro` pattern fixed per binder type.

A rule is a theorem whose conclusion is a `∀` telescope ending in an application of a parameter
`G`. Its premises are the binders up to the last one that mentions `G`, and its conclusion is the
rest. Take
```
theorem List.forall_mem_cons_intro {G : α → Prop} (ha : G a) (hl : ∀ x, x ∈ l → G x) :
    ∀ x, x ∈ a :: l → G x
```
with the conclusion `∀ x, x ∈ a :: l → G x`. It turns the target `∀ x ∈ [a, b], G x` into the
goals `G a` and `∀ x ∈ [b], G x`. The rules are keyed in a discrimination tree by their
conclusion, whose `∀` binders become `.arrow` keys over the binder type and the body. At each
binder of the target, `vcgen` applies the first matching rule in priority order as a backward rule
to the remaining target, and otherwise introduces the binder.

`vcgen` always uses the rule `Prod.forall_intro`. `Std.WP.Automation` also provides the rules
`PUnit.forall_intro` and `True.forall_intro`.
-/

open Lean Meta Sym

public section

namespace Lean.Elab.Tactic.VCGen

/-- One `@[vcgen_rintro]` rule: the theorem `declName`, whose first `numPremises` binders are the
premises, with the discrimination tree keys `keys` of its conclusion. -/
structure RIntroEntry where
  declName : Name
  numPremises : Nat
  keys : Array DiscrTree.Key
  prio : Nat
  deriving Inhabited

instance : BEq RIntroEntry where
  beq e₁ e₂ := e₁.declName == e₂.declName

/-- The rules `vcgen` uses without registration. -/
def builtinRIntros : Array Name := #[`Prod.forall_intro]

builtin_initialize rintroExt : SimpleScopedEnvExtension RIntroEntry (DiscrTree RIntroEntry) ←
  registerSimpleScopedEnvExtension {
    initial  := .empty
    addEntry := fun d e => d.insertKeyValue e.keys e
  }

/-- Check that the conclusion of `declName` is a `∀` telescope ending in an application of a
parameter, and compute its `RIntroEntry`. -/
def mkRIntroEntry (declName : Name) (prio : Nat) : MetaM RIntroEntry := do
  let info ← getConstInfo declName
  let (numBinders, numPremises) ← forallTelescope info.type fun xs body => do
    let some g := body.getAppFn.fvarId?
      | throwError "`@[vcgen_rintro]`: the conclusion of `{declName}` does not end in an \
          application of a parameter"
    let mut numPremises := 0
    for h : i in [:xs.size] do
      if xs[i].fvarId! == g || (← inferType xs[i]).containsFVar g then
        numPremises := i + 1
    return (xs.size, numPremises)
  if numPremises == numBinders then
    throwError "`@[vcgen_rintro]`: the conclusion of `{declName}` is not a `∀`"
  let rule ← mkBackwardRuleFromDecl declName (some numPremises)
  return { declName, numPremises, keys := rule.pattern.mkDiscrTreeKeys, prio }

/-- The entries of the rules of `builtinRIntros`, computed once. -/
builtin_initialize builtinRIntroEntries : IO.Ref (Std.HashMap Name RIntroEntry) ← IO.mkRef {}

/-- The rules registered with `@[vcgen_rintro]`, and the rules of `builtinRIntros` that exist in
the environment. -/
def getRIntros : MetaM (DiscrTree RIntroEntry) := do
  let mut d := rintroExt.getState (← getEnv)
  for declName in builtinRIntros do
    if (← getEnv).contains declName then
      let e ← match (← builtinRIntroEntries.get)[declName]? with
        | some e => pure e
        | none =>
          let e ← mkRIntroEntry declName (eval_prio default)
          builtinRIntroEntries.modify (·.insert declName e)
          pure e
      d := d.insertKeyValue e.keys e
  return d

builtin_initialize registerBuiltinAttribute {
  ref   := by exact decl_name%
  name  := `vcgen_rintro
  descr := "register a rule by which `vcgen` destructures a binder while introducing binders"
  add   := fun declName stx kind => do
    let prio ← getAttrParamOptPrio stx[1]
    let e ← (mkRIntroEntry declName prio).run'
    rintroExt.add e kind
}

end Lean.Elab.Tactic.VCGen
