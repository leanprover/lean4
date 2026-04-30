/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module
public import Lean.Elab
public import Lean.Meta
public meta import Lean.Elab
public meta import Lean.Meta
meta import Lean.Meta.Sym.Pattern
meta import Lean.Meta.Sym.Simp.DiscrTree

open Lean Meta Elab Tactic Sym
open Lean.Elab.Tactic.Do.SpecAttr
open Std.Do

/-!
Spec-theorem database used by `mvcgen'`. Mirrors the legacy `SpecTheorems` /
`SpecProof` API from `Lean.Elab.Tactic.Do.Attr` but indexes specs in a
`Sym.DiscrTree` keyed on the program's syntactic shape, with explicit
`SpecTheoremKind` (triple vs. simp) and per-spec eta-potential metadata.
-/

namespace Lean.Elab.Tactic.Do.SpecAttr

/--
The kind of a spec theorem.
-/
public inductive SpecTheoremKind where
  /--
  A Hoare triple spec: `⦃P⦄ prog ⦃Q⦄`.
  If `etaPotential` is non-zero, then the precondition contains meta variables that can be
  instantiated after applying `mintro ∀s` `etaPotential` many times.
  -/
  | triple (etaPotential : Nat := 0)
  /--
  A simp/equational spec: `lhs = rhs`.
  The pattern is the LHS.
  When matched, the VCGen rewrites the program from `lhs` to `rhs` and continues.
  `etaArgs` is the number of extra arguments introduced by eta-expanding function-level equations
  (e.g., class projection unfold lemmas). These args need `congrFun` at instantiation time.
  -/
  | simp (etaArgs : Nat := 0)
  deriving Inhabited

public structure SpecTheoremNew where
  /--
  Pattern for the program expression.
  This is the key used in the discrimination tree.
  If the proof has type `∀ a b c, Triple prog P Q`, then the pattern is `prog[a:=#2, b:=#1, c:=#0]`.
  For simp specs with type `∀ a b c, lhs = rhs`, the pattern is `lhs[a:=#2, b:=#1, c:=#0]`.
  -/
  pattern : Sym.Pattern
  /-- The proof for the theorem. -/
  proof : SpecProof
  /-- The kind of spec theorem: triple or simp. -/
  kind : SpecTheoremKind
  priority : Nat  := eval_prio default
  deriving Inhabited

public meta instance : BEq SpecTheoremNew where
  beq thm₁ thm₂ := thm₁.proof == thm₂.proof

/--
Like `SpecProof.instantiate`, but for simp specs also eta-expands function-level equations.

For unfold equations of class projections (e.g., `MonadState.modifyGet.eq_1`), the equation
after `forallMetaTelescope` may be between functions rather than values:
  `@modifyGet σ m self = self.3 : {α} → (σ → α × σ) → m α`
This method applies `congrFun` for each leading forall to reduce the equation to one between
values of type `m α`, introducing fresh metavariables for the extra arguments.
The number of extra args is stored in `SpecTheoremKind.simp etaArgs`.
-/
public meta def SpecTheoremNew.instantiate (specThm : SpecTheoremNew) :
    MetaM (Array Expr × Array BinderInfo × Expr × Expr) := do
  let (xs, bs, eqPrf, eqType) ← specThm.proof.instantiate
  let .simp etaArgs := specThm.kind | return (xs, bs, eqPrf, eqType)
  if etaArgs == 0 then return (xs, bs, eqPrf, eqType)
  let_expr Eq eqα _lhs _rhs := eqType | return (xs, bs, eqPrf, eqType)
  -- Eta-expand: introduce fresh metavars for leading foralls, then apply congrFun for each.
  let (extraXs, extraBs, _) ← withReducible <| forallMetaBoundedTelescope eqα etaArgs
  let eqPrf ← extraXs.foldlM (init := eqPrf) Meta.mkCongrFun
  let eqType ← inferType eqPrf
  return (xs ++ extraXs, bs ++ extraBs, eqPrf, eqType)

public structure SpecTheoremsNew where
  specs : DiscrTree SpecTheoremNew := DiscrTree.empty
  erased : PHashSet SpecProof := {}
  deriving Inhabited

public meta def mkTriplePatternFromExpr (expr : Expr) (levelParams : List Name := []) : SymM Pattern := do
  Prod.fst <$> Sym.mkPatternFromExprWithKey expr levelParams fun type => do
    let_expr Triple _m _ps _inst _α prog _P _Q := type | throwError "conclusion is not a Triple {indentExpr type}"
    return (prog, ())

public meta def mkSpecTheoremNew (proof : SpecProof) (prio : Nat) : SymM SpecTheoremNew := do
  -- cf. mkSimpTheoremCore
  let (levelParams, expr) ← proof.getProof
  let type ← Meta.inferType expr
  let type ← instantiateMVars type
  unless (← isProp type) do
    throwError "invalid 'spec', proposition expected{indentExpr type}"
  let pattern ← mkTriplePatternFromExpr expr levelParams
  withNewMCtxDepth do
  let (xs, _, type) ← withSimpGlobalConfig (forallMetaTelescopeReducing type)
  let type ← whnfR type
  let_expr c@Triple _m ps _inst _α _prog P _Q := type
    | throwError "unexpected kind of spec theorem; not a triple{indentExpr type}"
  -- beta potential of `P` describes how many times we want to `mintro ∀s`, that is,
  -- *eta*-expand the goal.
  let σs := mkApp (mkConst ``PostShape.args [c.constLevels![0]!]) ps
  let etaPotential ← computeMVarBetaPotentialForSPred xs σs P
  -- logInfo m!"Beta potential {etaPotential} for {P}"
  -- logInfo m!"mkSpecTheorem: {keys}, proof: {proof}"
  return { pattern, proof, kind := .triple etaPotential, priority := prio }

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
private meta def etaExpandEqPattern (pattern : Sym.Pattern) (eqTy : Expr) : Sym.Pattern × Nat :=
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
Create a `SpecTheoremNew` from a simp/equational declaration `declName : ∀ xs, lhs = rhs`.
The pattern is keyed on `lhs`.

For unfold equations of class projections (e.g., `MonadState.modifyGet.eq_1`), the equation
may be between functions rather than values. In that case, the pattern is eta-expanded
so the discrimination tree key includes all arguments.
-/
public meta def mkSpecTheoremNewFromSimpDecl? (declName : Name) (prio : Nat) : MetaM (Option SpecTheoremNew) := do
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

public meta def migrateSpecTheoremsDatabase (database : SpecTheorems) (simpThms : SimpTheorems) :
    SymM SpecTheoremsNew := do
  let mut specs : DiscrTree SpecTheoremNew := DiscrTree.empty
  for spec in database.specs.values do
    if database.isErased spec.proof then continue
    let newSpec ← mkSpecTheoremNew spec.proof spec.priority
    specs := Sym.insertPattern specs newSpec.pattern newSpec
  -- Migrate simp spec theorems (equational lemmas registered via `@[spec]`)
  for simpThm in simpThms.post.values do
    if let .decl declName .. := simpThm.origin then
      if simpThms.erased.contains simpThm.origin then continue
      try
        if let some newSpec ← mkSpecTheoremNewFromSimpDecl? declName simpThm.priority then
          specs := Sym.insertPattern specs newSpec.pattern newSpec
      catch e =>
        trace[Elab.Tactic.Do.vcgen] "Failed to migrate simp spec {declName}: {e.toMessageData}"
  -- Migrate definitions to unfold (registered via `attribute [spec] foo`)
  for declName in simpThms.toUnfold.toList do
    if simpThms.erased.contains (.decl declName) then continue
    let eqThms ← match simpThms.toUnfoldThms.find? declName with
      | some eqThms => pure eqThms
      | none =>
        -- No explicit equational theorems stored; generate them via `getEqnsFor?`
        let some eqThms ← liftMetaM <| Meta.getEqnsFor? declName | continue
        pure eqThms
    for eqThm in eqThms do
      try
        if let some newSpec ← mkSpecTheoremNewFromSimpDecl? eqThm (prio := eval_prio default) then
          specs := Sym.insertPattern specs newSpec.pattern newSpec
      catch e =>
        trace[Elab.Tactic.Do.vcgen] "Failed to migrate unfold spec {declName}/{eqThm}: {e.toMessageData}"
  return { database with specs }

/--
Look up `SpecTheoremNew`s in the `@[spec]` database.
Takes all specs that match the given program `e` and sorts by descending priority.
-/
public meta def SpecTheoremsNew.findSpecs (database : SpecTheoremsNew) (e : Expr) :
    SymM (Except (Array SpecTheoremNew) SpecTheoremNew) := do
  let e ← instantiateMVars e
  let e ← shareCommon e
  let candidates := Sym.getMatch database.specs e
  if h : candidates.size = 1 then return .ok candidates[0]
  -- It appears that insertion sort is *much* faster than qsort here.
  let candidates := candidates.insertionSort (·.priority > ·.priority)
  for spec in candidates do
    let some _res ← spec.pattern.match? e | continue
    return .ok spec
  return .error candidates

end Lean.Elab.Tactic.Do.SpecAttr
