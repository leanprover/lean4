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
Spec-theorem database used by `mvcgen'`. The `@[spec]` attribute already stores
`Std.Internal.Do` specs as pattern-keyed `SpecTheorem`s (see `Lean.Elab.Tactic.Do.Attr`);
this module adds the operations the VC generator needs on top: instantiating a spec to
`pre ⊑ wp …` form, migrating the equational lemmas registered through the `mvcgen_simp`
side of `@[spec]` into the same database, and looking up the specs matching a program.
-/

namespace Lean.Elab.Tactic.Do.Internal

open SpecAttr

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
Eta-expand a pattern for a function-level equation.

For unfold equations of class projections (e.g., `MonadState.modifyGet.eq_1`), the equation
may be between functions: `@modifyGet σ m self = self.3` of type `{α} → (σ → α × σ) → m α`.
The discrimination tree key includes the arg count, so lookup would fail if the pattern has
fewer args than the actual fully-applied program.

This function takes a pattern (keyed on the LHS), the equation type `eqTy`, and:
1. Decomposes leading foralls of `eqTy` to find the extra argument domains
2. Extends `varTypes` with those domains
3. Applies the extra bvars to the pattern expression (lifting existing bvars accordingly)

Returns the eta-expanded pattern and the number of extra args (0 if no expansion needed).
-/
private def etaExpandEqPattern (pattern : Sym.Pattern) (eqTy : Expr) : Sym.Pattern × Nat :=
  if !eqTy.isForall then (pattern, 0)
  else
    -- Collect forall domains from eqTy
    let rec collectDomains (ty : Expr) (acc : Array Expr) : Array Expr :=
      if let .forallE _ d b _ := ty then collectDomains b (acc.push d) else acc
    let extraDomains := collectDomains eqTy #[]
    let k := extraDomains.size
    -- Lift existing bvars in pattern by k, then apply new bvars #(k-1) ... #0
    let liftedPattern := pattern.pattern.liftLooseBVars 0 k
    let newBVars := Array.ofFn (n := k) fun i => mkBVar (k - 1 - i)
    let newPatternExpr := mkAppN liftedPattern newBVars
    -- Conservatively reset metadata (varInfos?, checkTypeMask?) since we can't
    -- call the private helpers from here. fnInfos is unchanged (same constants).
    let newPattern : Sym.Pattern :=
      { pattern with
        varTypes := pattern.varTypes ++ extraDomains
        pattern := newPatternExpr
        varInfos? := none
        checkTypeMask? := none }
    (newPattern, k)

/--
Create a `SpecTheorem` from a simp/equational declaration `declName : ∀ xs, lhs = rhs`.
The pattern is keyed on `lhs`.

For unfold equations of class projections (e.g., `MonadState.modifyGet.eq_1`), the equation
may be between functions rather than values. In that case, the pattern is eta-expanded
so the discrimination tree key includes all arguments.
-/
public def mkSpecTheoremFromSimpDecl? (declName : Name) (prio : Nat) : MetaM (Option SpecTheorem) := do
  let (pattern, (eqTy, rhs)) ← Sym.mkPatternFromDeclWithKey declName fun body => do
    let_expr Eq eqTy lhs rhs := body | throwError "conclusion is not an equality{indentExpr body}"
    return (lhs, (eqTy, rhs))
  let (pattern, etaArgs) := etaExpandEqPattern pattern eqTy
  -- Skip no-op equations where LHS and RHS are the same after `unfoldReducible`.
  -- E.g., `getThe.eq_1 : getThe σ = MonadStateOf.get` becomes a no-op because
  -- `preprocessDeclPattern` unfolds `getThe` to `MonadStateOf.get`.
  -- We use `==` (structural equality) rather than `isSameExpr` (pointer equality)
  -- because the LHS and RHS are independently constructed.
  -- Compare the original (non-expanded) pattern with rhs, since both are in the same context.
  if etaArgs == 0 && pattern.pattern == rhs then return none
  return some { pattern, proof := .global declName, kind := .simp etaArgs, priority := prio }

/--
Extend the `@[spec]` database with the equational lemmas registered through the `mvcgen_simp`
side of `@[spec]`:
- simp theorem declarations registered directly as `@[spec]`,
- unfold entries registered with `attribute [spec] foo`, using stored equation lemmas when
  available and falling back to `Meta.getEqnsFor?`.

Hoare triple and `⊑ wp` specs need no migration: the attribute stores them pattern-keyed
at annotation time.
-/
public def migrateSpecTheoremsDatabase (database : SpecTheorems) (simpThms : SimpTheorems) :
    SymM SpecTheorems := do
  let mut specs := database.specs
  -- Erased entries are still inserted into `specs` below; `findSpecs` filters them out
  -- at lookup time.
  let erased : PHashSet SpecProof := simpThms.erased.fold (init := database.erased) fun acc o =>
    match SpecProof.ofOrigin o with
    | some p => acc.insert p
    | none => acc
  -- Migrate simp spec theorems (equational lemmas registered via `@[spec]`)
  for simpThm in simpThms.post.values do
    if let .decl declName .. := simpThm.origin then
      try
        if let some newSpec ← mkSpecTheoremFromSimpDecl? declName simpThm.priority then
          specs := Sym.insertPattern specs newSpec.pattern newSpec
      catch e =>
        trace[Elab.Tactic.Do.vcgen] "Failed to migrate simp spec {declName}: {e.toMessageData}"
  -- Migrate definitions to unfold (registered via `attribute [spec] foo`)
  for declName in simpThms.toUnfold.toList do
    let eqThms ← match simpThms.toUnfoldThms.find? declName with
      | some eqThms => pure eqThms
      | none =>
        -- No explicit equational theorems stored; generate them via `getEqnsFor?`
        let some eqThms ← liftMetaM <| Meta.getEqnsFor? declName | continue
        pure eqThms
    for eqThm in eqThms do
      try
        if let some newSpec ← mkSpecTheoremFromSimpDecl? eqThm (prio := eval_prio default) then
          specs := Sym.insertPattern specs newSpec.pattern newSpec
      catch e =>
        trace[Elab.Tactic.Do.vcgen] "Failed to migrate unfold spec {declName}/{eqThm}: {e.toMessageData}"
  return { specs, erased }

end VCGen

/--
Look up `SpecTheorem`s in the `@[spec]` database.
Takes all specs that match the given program `e` and sorts by descending priority.
-/
public def SpecAttr.SpecTheorems.findSpecs (database : SpecTheorems) (e : Expr) :
    SymM (Except (Array SpecTheorem) SpecTheorem) := do
  let e ← instantiateMVars e
  let e ← shareCommon e
  let candidates := Sym.getMatch database.specs e
  let candidates := candidates.filter fun spec => !database.erased.contains spec.proof
  if h : candidates.size = 1 then
    have : 0 < candidates.size := h ▸ Nat.zero_lt_one
    return .ok candidates[0]
  -- It appears that insertion sort is *much* faster than qsort here.
  let candidates := candidates.insertionSort (·.priority > ·.priority)
  for spec in candidates do
    let some _res ← spec.pattern.match? e | continue
    return .ok spec
  return .error candidates

end Lean.Elab.Tactic.Do.Internal
