/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Vladimir Gladshtein
-/
module

prelude
public import Lean.Elab.Tactic.Do.Attr
public import Lean.Meta.Sym.Pattern
public import Lean.Meta.DiscrTree.Util
import Lean.Meta.Sym.Simp.DiscrTree
import Lean.Meta.Sym.Util

open Lean Meta Elab Tactic Sym

/-!
Spec-theorem database used by `vcgen`. The `@[spec]` attribute already stores
`Std.Internal.Do` specs as pattern-keyed `SpecTheorem`s (see `Lean.Elab.Tactic.Do.Attr`);
this module adds the operations the VC generator needs on top: instantiating a spec to
`pre ⊑ wp …` form, migrating the equational lemmas registered through the `mvcgen_simp`
side of `@[spec]` into the same database, and looking up the specs matching a program.
-/

namespace Lean.Elab.Tactic.Do.Internal

open SpecAttr

/-- Returns `true` if `e` is already internalized into the current `SymM` share table, in which case
`shareCommon e` returns `e` unchanged. -/
public def _root_.Lean.Meta.Sym.isShared (e : Expr) : SymM Bool :=
  return (← get).share.set.contains { expr := e }

/--
Internalizes the pattern's expressions into the current `SymM` share table.

A pattern is built in `MetaM`, outside the `SymM` thread whose table the targets are internalized
into, so its closed subterms (the instance telescope of a `wp` application, for example) are
structurally equal to but distinct from the targets'. Internalizing the pattern once makes those
subterms pointer-equal to every target internalized afterwards, so matching them is `O(1)`.
-/
public def _root_.Lean.Meta.Sym.Pattern.shareCommon (p : Pattern) : SymM Pattern := do
  return { p with
    pattern := ← Sym.shareCommon p.pattern
    varTypes := ← p.varTypes.mapM Sym.shareCommon }

/--
Instantiates a spec theorem's proof.

Hoare triple and `⊑ wp` specs are normalised to `pre ⊑ wp …` form via `tripleToWpProof?`.
Simp specs keep the raw `lhs = rhs` equality, but eta-expand function-level equations:
for unfold equations of class projections (e.g., `MonadState.modifyGet.eq_1`), the equation
after `forallMetaTelescope` may be between functions rather than values:
  `@modifyGet σ m self = self.3 : {α} → (σ → α × σ) → m α`
This method applies `congrFun` for each leading forall to reduce the equation to one between
values of type `m α`, introducing fresh metavariables for the extra arguments.
The number of extra args is stored in `SpecTheoremKind.simp etaArgs`.
-/
public def SpecAttr.SpecTheorem.instantiate (specThm : SpecTheorem) :
    MetaM (Array Expr × Array BinderInfo × Expr × Expr) := do
  let (xs, bs, prf, type) ← specThm.proof.instantiate
  let .simp etaArgs := specThm.kind
    | do
      let some (prf, type) ← tripleToWpProof? prf type
        | throwError "expected `Triple` or `⊑ wp` specification, got{indentExpr type}"
      return (xs, bs, prf, type)
  if etaArgs == 0 then return (xs, bs, prf, type)
  let_expr Eq eqα _lhs _rhs := type | return (xs, bs, prf, type)
  -- Eta-expand: introduce fresh metavars for leading foralls, then apply congrFun for each.
  let (extraXs, extraBs, _) ← withReducible <| forallMetaBoundedTelescope eqα etaArgs
  let prf ← extraXs.foldlM (init := prf) Meta.mkCongrFun
  let type ← inferType prf
  return (xs ++ extraXs, bs ++ extraBs, prf, type)

/-- The declaration name of a global spec theorem, `none` for local/syntactic specs. -/
public def SpecAttr.SpecTheorem.global? (specThm : SpecTheorem) : Option Name :=
  match specThm.proof with | .global decl => some decl | _ => none

namespace VCGen

/--
Extend the `@[spec]` database with the equational lemmas registered through the `mvcgen_simp`
side of `@[spec]`:
- simp theorem declarations registered directly as `@[spec]`,
- unfold entries registered with `attribute [spec] foo`, using stored equation lemmas when
  available and falling back to `Meta.getEqnsFor?`.

Hoare triple and `⊑ wp` specs are already in `database`: the attribute stores them pattern-keyed
at annotation time.
-/
public def extendWithSimpSpecs (database : SpecTheorems) (simpThms : SimpTheorems) :
    MetaM SpecTheorems := do
  let mut specs := database.specs
  -- Erased entries are still inserted into `specs` below; `findSpecs` filters them out
  -- at lookup time.
  let erased : PHashSet SpecProof := simpThms.erased.fold (init := database.erased) fun acc o =>
    match SpecProof.ofOrigin o with
    | some p => acc.insert p
    | none => acc
  -- Add simp spec theorems (equational lemmas registered via `@[spec]`)
  for simpThm in simpThms.post.values do
    if let .decl declName .. := simpThm.origin then
      try
        if let some newSpec ← mkSpecTheoremFromSimpDecl? declName simpThm.priority then
          specs := Sym.insertPattern specs newSpec.pattern newSpec
      catch e =>
        trace[Elab.Tactic.Do.vcgen] "Failed to add simp spec {declName}: {e.toMessageData}"
  -- Add definitions to unfold (registered via `attribute [spec] foo`)
  for declName in simpThms.toUnfold.toList do
    let eqThms ← match simpThms.toUnfoldThms.find? declName with
      | some eqThms => pure eqThms
      | none =>
        -- No explicit equational theorems stored; generate them via `getEqnsFor?`
        let some eqThms ← Meta.getEqnsFor? declName | continue
        pure eqThms
    for eqThm in eqThms do
      try
        if let some newSpec ← mkSpecTheoremFromSimpDecl? eqThm (prio := eval_prio default) then
          specs := Sym.insertPattern specs newSpec.pattern newSpec
      catch e =>
        trace[Elab.Tactic.Do.vcgen] "Failed to add unfold spec {declName}/{eqThm}: {e.toMessageData}"
  return { specs, erased }

end VCGen

/--
Look up `SpecTheorem`s in the `@[spec]` database.
Takes all specs that match the given program `e` and sorts by descending priority.
-/
public def SpecAttr.SpecTheorems.findSpecs (database : SpecTheorems) (e : Expr) :
    SymM (Except (Array SpecTheorem) SpecTheorem × SpecTheorems) := do
  let e ← instantiateMVars e
  let e ← shareCommon e
  let candidates := Sym.getMatch database.specs e
  let candidates := candidates.filter fun spec => !database.erased.contains spec.proof
  if h : candidates.size = 1 then
    have : 0 < candidates.size := h ▸ Nat.zero_lt_one
    return (.ok candidates[0], database)
  -- It appears that insertion sort is *much* faster than qsort here.
  let candidates := candidates.insertionSort (·.priority > ·.priority)
  let mut database := database
  for spec in candidates do
    -- Match against the internalized pattern so its instance arguments are pointer-equal to the
    -- program's. A spec is internalized the first time it is tried and stored back in the database,
    -- so later lookups find it already in the share table and skip the work.
    let mut spec := spec
    unless ← isShared spec.pattern.pattern do
      spec := { spec with pattern := ← spec.pattern.shareCommon }
      -- Take sole ownership of the discrimination tree before inserting so the update is in place.
      let specs := database.specs
      database := { database with specs := default }
      database := { database with specs := Sym.insertPattern specs spec.pattern spec }
    let some _res ← spec.pattern.match? e | continue
    return (.ok spec, database)
  return (.error candidates, database)

end Lean.Elab.Tactic.Do.Internal
