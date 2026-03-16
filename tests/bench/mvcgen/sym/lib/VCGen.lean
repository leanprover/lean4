/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module
public import Lean.Elab
public import Lean.Meta
public import Lean.Parser
public import Lean.Expr
public meta import Lean.Elab
public meta import Lean.Meta
public meta import Lean.Meta.Match.Rewrite
public meta import Lean.Elab.Tactic.Do.VCGen.Split
meta import Lean.Meta.Sym.Pattern
meta import Lean.Meta.Sym.Simp.DiscrTree

open Lean Parser Meta Elab Tactic Sym
open Lean.Elab.Tactic.Do.SpecAttr
open Std.Do

/-!
Creating backward rules for registered specifications
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
  -/
  | simp
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

meta instance : BEq SpecTheoremNew where
  beq thm₁ thm₂ := thm₁.proof == thm₂.proof

public structure SpecTheoremsNew where
  specs : DiscrTree SpecTheoremNew := DiscrTree.empty
  erased : PHashSet SpecProof := {}
  deriving Inhabited

meta def mkTriplePatternFromExpr (expr : Expr) (levelParams : List Name := []) : SymM Pattern := do
  Prod.fst <$> Sym.mkPatternFromExprWithKey expr levelParams fun type => do
    let_expr Triple _m _ps _inst _α prog _P _Q := type | throwError "conclusion is not a Triple {indentExpr type}"
    return (prog, ())

meta def mkSpecTheoremNew (proof : SpecProof) (prio : Nat) : SymM SpecTheoremNew := do
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
Create a `SpecTheoremNew` from a simp/equational declaration `declName : ∀ xs, lhs = rhs`.
The pattern is keyed on `lhs`.
-/
meta def mkSpecTheoremNewFromSimpDecl? (declName : Name) (prio : Nat) : MetaM (Option SpecTheoremNew) := do
  let (pattern, rhs) ← Sym.mkEqPatternFromDecl declName
  -- Skip no-op equations where LHS and RHS are the same after `unfoldReducible`.
  -- E.g., `getThe.eq_1 : getThe σ = MonadStateOf.get` becomes a no-op because
  -- `preprocessDeclPattern` unfolds `getThe` to `MonadStateOf.get`.
  -- We use `==` (structural equality) rather than `isSameExpr` (pointer equality)
  -- because the LHS and RHS are independently constructed.
  if pattern.pattern == rhs then return none
  return some { pattern, proof := .global declName, kind := .simp, priority := prio }

meta def migrateSpecTheoremsDatabase (database : SpecTheorems) (simpThms : SimpTheorems) :
    SymM SpecTheoremsNew := do
  let mut specs : DiscrTree SpecTheoremNew := DiscrTree.empty
  for spec in database.specs.values do
    let newSpec ← mkSpecTheoremNew spec.proof spec.priority
    specs := Sym.insertPattern specs newSpec.pattern newSpec
  -- Migrate simp spec theorems (equational lemmas registered via `@[spec]`)
  for simpThm in simpThms.post.values do
    if let .decl declName .. := simpThm.origin then
      try
        if let some newSpec ← mkSpecTheoremNewFromSimpDecl? declName simpThm.priority then
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
        if let some newSpec ← mkSpecTheoremNewFromSimpDecl? eqThm (prio := eval_prio default) then
          specs := Sym.insertPattern specs newSpec.pattern newSpec
      catch e =>
        trace[Elab.Tactic.Do.vcgen] "Failed to migrate unfold spec {declName}/{eqThm}: {e.toMessageData}"
  return { database with specs }

/--
Look up `SpecTheoremNew`s in the `@[spec]` database.
Takes all specs that match the given program `e` and sorts by descending priority.
-/
meta def SpecTheoremsNew.findSpecs (database : SpecTheoremsNew) (e : Expr) :
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


-- Normalize universe levels in an expression so that `max u v` and `max v u` have a canonical
-- representation. This is needed because backward rule pattern matching is structural and
-- level expressions from different sources (e.g., instance synthesis, type inference) may have
-- different but equivalent `max` orderings.
meta def normalizeLevelsExpr (e : Expr) : CoreM Expr :=
  Core.transform e (pre := fun e => do
    match e with
    | .sort u => return .done <| e.updateSort! u.normalize
    | .const _ us => return .done <| e.updateConst! (us.map Level.normalize)
    | _ => return .continue)

/-- Build goal: `P ⊢ₛ wp⟦prog⟧ Q ss...`. Meant to be partially applied for convenience. -/
private meta def mkGoal (u v : Level) (m σs ps instWP α : Expr) (ss : Array Expr) (P Q : Expr) (prog : Expr) : Expr :=
  mkApp3 (mkConst ``SPred.entails [u]) σs P
    (mkAppN (mkApp4 (mkConst ``PredTrans.apply [u]) ps α
      (mkApp5 (mkConst ``WP.wp [u, v]) m ps instWP α prog) Q) ss)

/-- Extract the program from a goal built by `mkGoal`. -/
private meta def extractProgFromGoal (goal : Expr) : Expr :=
  goal.getArg! 2 |>.getArg! 2 |>.getArg! 4

/--
Create a backward rule for the `SpecTheoremNew` that was looked up in the database.
In order for the backward rule to apply, we need to instantiate both `m` and `ps` with the ones
given by the use site, and perhaps emit verification conditions for spec lemmas that would not
apply everywhere.

### General idea

Consider the spec theorem `Spec.bind`:
```
Spec.bind : ∀ {m : Type u → Type v} {ps : PostShape} [inst : Monad m] [inst_1 : WPMonad m ps]
  {α β : Type u} {x : m α} {f : α → m β} {Q : PostCond β ps},
  ⦃wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.snd)⦄ (x >>= f) ⦃Q⦄
```
This theorem is already in "WP-form", so its postcondition `Q` is schematic (i.e., a ∀-bound var).
However, its precondition `wp⟦x⟧ ...` is not. Hence we must emit a VC for the precondition:
```
prf : ∀ {m : Type u → Type v} {ps : PostShape} [inst : Monad m] [inst_1 : WPMonad m ps]
  {α β : Type u} {x : m α} {f : α → m β} {Q : PostCond β ps}
  (P : Assertion ps) (hpre : P ⊢ₛ wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.snd)),
  P ⊢ₛ wp⟦x >>= f⟧ Q
```
(Note that `P ⊢ₛ wp⟦x >>= f⟧ Q` is the definition of `⦃P⦄ (x >>= f) ⦃Q⦄`.)
Where `prf` is constructed by doing `SPred.entails.trans hpre spec` under the forall telescope.
The conclusion of this rule applies to any situation where `bind` is the top-level symbol in the
program.

Similarly, a VC is generated for the postcondition if it isn't schematic.

Furthermore, when there are excess state arguments `[s₁, ..., sₙ]` involved, we rather need to
specialize the backward rule for that:
```
... : ∀ {m : Type u → Type v} {ps : PostShape} [inst : Monad m] [inst_1 : WPMonad m ps]
  {α β : Type u} {x : m α} {f : α → m β} {Q : PostCond β ps}
  (P : Assertion ...) (hpre : P ⊢ₛ wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.snd) s₁ ... sₙ),
  P ⊢ₛ wp⟦x >>= f⟧ Q s₁ ... sₙ
```

### Caching

It turns out we can cache backward rules for the cache key `(specThm, m, excessArgs.size)`.
This is very important for performance and helps getting rid of the overhead imposed by the
generality of `Std.Do`. We do that in the `VCGenM` wrapper `mkBackwardRuleFromSpecCached`.
Furthermore, in order to avoid re-checking the same proof in the kernel, we generate an auxiliary
lemma for the backward rule.

### Specialization and unfolding of `Std.Do` abbreviations and defs

It is unnecessary to use the `bind` rule in full generality. It is much more efficient to specialize
it for the particular monad, postshape and `WP` instance. In doing so we can also unfold many
`Std.Do` abbrevations, such as `Assertion ps` and `PostCond α ps`.
We do that by doing `unfoldReducible` on the forall telescope. The type for `StateM Nat` and one
excess state arg `s` becomes
```
prf : ∀ (α : Type) (x : StateT Nat Id α) (β : Type) (f : α → StateT Nat Id β)
        (Q : (β → Nat → ULift Prop) × ExceptConds (PostShape.arg Nat PostShape.pure)) (s : Nat)
        (P : ULift Prop) (hpre : P ⊢ₛ wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.snd) s),
        P ⊢ₛ wp⟦x >>= f⟧ Q s
```
We are still investigating how to get rid of more unfolding overhead, such as for `wp` and
`List.rec`.
-/
meta def mkBackwardRuleFromSpec (specThm : SpecTheoremNew) (m σs ps instWP : Expr) (excessArgs : Array Expr) : SymM BackwardRule := do
  let preprocessExpr : Expr → SymM Expr := shareCommon <=< liftMetaM ∘ unfoldReducible
  -- Create a backward rule for the spec we look up in the database.
  -- In order for the backward rule to apply, we need to instantiate both `m` and `ps` with the ones
  -- given by the use site.
  let (xs, _bs, spec, specTy) ← specThm.proof.instantiate
  let_expr f@Triple m' ps' instWP' α prog P Q := specTy
    | liftMetaM <| throwError "target not a Triple application {specTy}"
  -- Reject the spec and try the next if the monad doesn't match.
  unless ← isDefEqGuarded m m' do -- TODO: Try isDefEqS?
    throwError "Post program defeq Monad mismatch: {m} ≠ {m'}"
  unless ← isDefEqGuarded ps ps' do
    throwError "Post program defeq Postshape mismatch: {ps} ≠ {ps'}"
  unless ← isDefEqGuarded instWP instWP' do
    throwError "Post program defeq WP instance mismatch: {instWP} ≠ {instWP'}"

  -- We must ensure that P and Q are pattern variables so that the spec matches for every potential
  -- P and Q. We do so by introducing VCs accordingly.
  -- The following code could potentially be extracted into a definition at @[spec] attribute
  -- annotation time. That might help a bit with kernel checking time.
  let excessArgNamesTypes ← excessArgs.mapM fun arg =>
    return (← mkFreshUserName `s, ← Meta.inferType arg)
  let spec ← withLocalDeclsDND excessArgNamesTypes fun ss => do
    let needPreVC := !excessArgs.isEmpty || !xs.contains P
    let needPostVC := !xs.contains Q
    let us := f.constLevels!
    let u := us[0]!
    let wp := mkApp5 (mkConst ``WP.wp us) m ps instWP α prog
    let wpApplyQ := mkApp4 (mkConst ``PredTrans.apply [u]) ps α wp Q  -- wp⟦prog⟧ Q
    let Pss := mkAppN P ss  -- P s₁ ... sₙ
    let typeP ← preprocessExpr (mkApp (mkConst ``SPred [u]) σs)
      -- Note that this is the type of `P s₁ ... sₙ`,
      -- which is `Assertion ps'`, but we don't know `ps'`
    let typeQ ← preprocessExpr (mkApp2 (mkConst ``PostCond [u]) α ps)
    let mut declInfos := #[]
    if needPreVC then
      let nmP' ← mkFreshUserName `P
      let nmHPre ← mkFreshUserName `hpre
      let entailment P' := preprocessExpr <| mkApp3 (mkConst ``SPred.entails [u]) σs P' Pss
      declInfos := #[(nmP', .default, fun _ => pure typeP),
                     (nmHPre, .default, fun xs => entailment xs.back!)]
    if needPostVC then
      let nmQ' ← mkFreshUserName `Q
      let nmHPost ← mkFreshUserName `hpost
      let entailment Q' := preprocessExpr <| mkApp4 (mkConst ``PostCond.entails [u]) α ps Q Q'
      declInfos := declInfos ++
                   #[(nmQ', .default, fun _ => pure typeQ),
                     (nmHPost, .default, fun xs => entailment xs.back!)]
    withLocalDecls declInfos fun ys => liftMetaM ∘ mkLambdaFVars (ss ++ ys) =<< do
      if !needPreVC && !needPostVC && excessArgs.isEmpty then
        -- Still need to unfold the triple in the spec type
        let entailment ← preprocessExpr <| mkApp3 (mkConst ``SPred.entails [u]) σs P wpApplyQ
        let prf ← mkExpectedTypeHint spec entailment
        -- check prf
        return prf
      let mut prf := spec
      let P := Pss  -- P s₁ ... sₙ
      let wpApplyQ := mkAppN wpApplyQ ss  -- wp⟦prog⟧ Q s₁ ... sₙ
      prf := mkAppN prf ss -- Turn `⦃P⦄ prog ⦃Q⦄` into `P s₁ ... sₙ ⊢ₛ wp⟦prog⟧ Q s₁ ... sₙ`
      let mut newP := P
      let mut newQ := Q
      if needPreVC then
        -- prf := hpre.trans prf
        let P' := ys[0]!
        let hpre := ys[1]!
        prf := mkApp6 (mkConst ``SPred.entails.trans [u]) σs P' P wpApplyQ hpre prf
        newP := P'
        -- check prf
      if needPostVC then
        -- prf := prf.trans <| (wp x).mono _ _ hpost
        let wp := mkApp5 (mkConst ``WP.wp f.constLevels!) m ps instWP α prog
        let Q' := ys[ys.size-2]!
        let hpost := ys[ys.size-1]!
        let wpApplyQ' := mkApp4 (mkConst ``PredTrans.apply [u]) ps α wp Q' -- wp⟦prog⟧ Q'
        let wpApplyQ' := mkAppN wpApplyQ' ss -- wp⟦prog⟧ Q' s₁ ... sₙ
        let hmono := mkApp6 (mkConst ``PredTrans.mono [u]) ps α wp Q Q' hpost
        let hmono := mkAppN hmono ss
        prf := mkApp6 (mkConst ``SPred.entails.trans [u]) σs newP wpApplyQ wpApplyQ' prf hmono
        newQ := Q'
        -- check prf
      return prf
  -- We use `mkBackwardRuleFromExpr` instead of `mkAuxLemma` + `mkBackwardRuleFromDecl` because
  -- the proof may contain free variables from the goal context (e.g., generic `m`, `ps`),
  -- which would cause `mkAuxLemma`'s `addDecl` to fail with a kernel error.
  let spec ← instantiateMVars spec
  let res ← abstractMVars spec
  -- Normalize levels so structural matching in `BackwardRule.apply` succeeds even when
  -- different code paths produce `max u v` vs `max v u` (semantically equal but structurally not).
  let expr ← normalizeLevelsExpr res.expr
  mkBackwardRuleFromExpr expr res.paramNames.toList

/--
Create a backward rule for a simp/equational spec `∀ xs, lhs = rhs`.

Instantiates the equation, unifies with the monad `m`, synthesizes typeclass instances,
reduces projections and applies `unfoldReducible` to the RHS. Then builds a backward rule
of the form:
```
∀ Q s₁ ... sₙ P (h : P ⊢ₛ wp⟦rhs_reduced⟧ Q s₁ ... sₙ), P ⊢ₛ wp⟦lhs⟧ Q s₁ ... sₙ
```
using `Eq.mpr` with a `congrArg` proof.

For example, `MonadState.get.eq_1 : get = self.1` with `m = StateT σ m'` yields a rule
that rewrites `wp⟦get⟧` to `wp⟦MonadStateOf.get⟧` (after instance synthesis + projection
reduction + unfoldReducible).
-/
meta def mkBackwardRuleFromSimpSpec (specThm : SpecTheoremNew) (m σs ps instWP : Expr)
    (excessArgs : Array Expr) : SymM BackwardRule := do
  let preprocessExpr : Expr → SymM Expr := shareCommon <=< liftMetaM ∘ unfoldReducible
  let wpType ← liftMetaM <| Meta.inferType instWP
  let us := wpType.getAppFn.constLevels!
  let u := us[0]!
  let v := us[1]!
  let (xs, _, eqPrf, eqType) ← specThm.proof.instantiate
  let_expr Eq eqα lhs rhs := eqType
    | liftMetaM <| throwError "simp spec is not an equation: {eqType}"
  let α ← mkFreshExprMVar (mkSort u.succ)
  unless ← isDefEqGuarded eqα (mkApp m α) do
    throwError "Simp spec: could not unify equation type {eqα} with {mkApp m α}"
  for x in xs do
    if x.isMVar && !(← x.mvarId!.isAssigned) then
      let xType ← Meta.inferType x
      try liftMetaM <| Meta.synthInstance xType >>= x.mvarId!.assign catch _ => pure ()
  let eqPrf ← instantiateMVarsS eqPrf
  let lhs ← instantiateMVarsS lhs
  let rhs ← instantiateMVarsS rhs
  -- Reduce projections (e.g., `inst.1` → `getThe σ` when inst is a concrete dictionary).
  let rhs ← liftMetaM <| Meta.transform rhs (pre := fun e => do
    if let .proj .. := e then
      if let some r ← withDefault <| Meta.reduceProj? e then return .done r
    return .continue)
  let rhs ← shareCommon (← liftMetaM <| unfoldReducible rhs)
  -- Build the backward rule
  let excessArgNamesTypes ← excessArgs.mapM fun arg =>
    return (← mkFreshUserName `s, ← Meta.inferType arg)
  let typeQ ← preprocessExpr (mkApp2 (mkConst ``PostCond [u]) α ps)
  let spec ←
    withLocalDeclD `Q typeQ fun Q => do
    withLocalDeclsDND excessArgNamesTypes fun ss => do
    let mkWpApplyQss prog := do
      let wp ← Sym.Internal.mkAppS₅ (mkConst ``WP.wp [u, v]) m ps instWP α prog
      let mut t ← Sym.Internal.mkAppS₄ (mkConst ``PredTrans.apply [u]) ps α wp Q
      for s in ss do t ← Sym.Internal.mkAppS t s
      pure t
    let lhsWp ← mkWpApplyQss lhs
    let rhsWp ← mkWpApplyQss rhs
    let typeP ← preprocessExpr (mkApp (mkConst ``SPred [u]) σs)
    withLocalDeclD `P typeP fun P => do
    let conclusionType ← preprocessExpr <| mkApp3 (mkConst ``SPred.entails [u]) σs P lhsWp
    let premiseType ← preprocessExpr <| mkApp3 (mkConst ``SPred.entails [u]) σs P rhsWp
    withLocalDeclD `h premiseType fun h => do
    -- Build: Eq.mpr (congrArg motive eqPrf) h
    -- motive = fun prog => P ⊢ₛ wp⟦prog⟧ Q s₁ ... sₙ
    let mα ← instantiateMVarsS (mkApp m α)
    let motiveBody := mkApp3 (mkConst ``SPred.entails [u]) σs P
      (mkAppN (mkApp4 (mkConst ``PredTrans.apply [u]) ps α
        (mkApp5 (mkConst ``WP.wp [u, v]) m ps instWP α (.bvar 0)) Q) ss)
    let motive := Expr.lam `prog mα motiveBody .default
    let eqProof ← liftMetaM <| Meta.mkCongrArg motive eqPrf
    let prf := mkApp4 (mkConst ``Eq.mpr [0]) conclusionType premiseType eqProof h
    liftMetaM <| mkLambdaFVars (#[Q] ++ ss ++ #[P, h]) prf
  let spec ← instantiateMVars spec
  let res ← abstractMVars spec
  -- Normalize universe levels so the backward rule's pattern matches structurally.
  let expr ← normalizeLevelsExpr res.expr
  mkBackwardRuleFromExpr expr res.paramNames.toList

open Lean.Elab.Tactic.Do in
/--
Creates a reusable backward rule for splitting `ite`, `dite`, or matchers.

Uses `SplitInfo.withAbstract` to open fvars for the split, then `SplitInfo.splitWith`
to build the splitting proof. Hypothesis types are discovered via `rwIfOrMatcher` inside
the splitter telescope.
-/
meta def mkBackwardRuleForSplit (splitInfo : SplitInfo) (m σs ps instWP : Expr) (excessArgs : Array Expr) : SymM BackwardRule := do
  let preprocessExpr : Expr → SymM Expr := shareCommon <=< liftMetaM ∘ unfoldReducible
  let us := instWP.getAppFn.constLevels!
  let u := us[0]!
  let v := us[1]!
  let prf ←
    withLocalDeclD `α (mkSort u.succ) fun α => do
    let mα ← preprocessExpr <| mkApp m α
    splitInfo.withAbstract mα fun abstractInfo splitFVars => do
    -- Eta-reduce alts so the backward rule pattern uses clean fvar alts, avoiding expensive
    -- higher-order unification. The alts are eta-expanded in `withAbstract` so that
    -- `splitWith`/`matcherApp.transform` can `instantiateLambda` them.
    let abstractProg := match abstractInfo with
      | .ite e | .dite e => e
      | .matcher matcherApp =>
        { matcherApp with alts := matcherApp.alts.map Expr.eta }.toExpr
    let excessArgNamesTypes ← excessArgs.mapM fun arg => return (`s, ← Meta.inferType arg)
    withLocalDeclsDND excessArgNamesTypes fun ss => do
    withLocalDeclD `P (← preprocessExpr <| mkApp (mkConst ``SPred [u]) σs) fun P => do
    withLocalDeclD `Q (← preprocessExpr <| mkApp2 (mkConst ``PostCond [u]) α ps) fun Q => do
    let mkGoal := mkGoal u v m σs ps instWP α ss P Q
    -- Subgoal types are synthetic opaque metavariables, filled in the `splitWith` callback below.
    -- Synthetic opaque so that `rwIfOrMatcher`'s `assumption` tactic cannot assign them.
    let subgoals ← splitInfo.altInfos.mapM fun _ =>
      liftMetaM <| mkFreshExprSyntheticOpaqueMVar (mkSort 0)
    let namedSubgoals := subgoals.mapIdx fun i mv => ((`h).appendIndexAfter (i+1), mv)
    withLocalDeclsDND namedSubgoals fun subgoalHyps => do
    let prf ← liftMetaM <|
      abstractInfo.splitWith
        (useSplitter := true)
        (mkGoal abstractProg)
        (fun _name bodyType idx altFVars => do
          let prog := extractProgFromGoal bodyType
          let res ← rwIfOrMatcher idx prog
          if res.proof?.isNone then
            throwError "mkBackwardRuleForSplit: rwIfOrMatcher failed for alt {idx}\n{indentExpr prog}"
          let boundFVars := altFVars.all
          subgoals[idx]!.mvarId!.assign (← mkForallFVars boundFVars (mkGoal res.expr))
          let context ← withLocalDecl `e .default mα fun e =>
            mkLambdaFVars #[e] (mkGoal e)
          (← Simp.mkCongrArg context res).mkEqMPR (mkAppN subgoalHyps[idx]! boundFVars))
    mkLambdaFVars (#[α] ++ splitFVars ++ ss ++ #[P, Q] ++ subgoalHyps) prf
  let prf ← instantiateMVars prf
  let res ← abstractMVars prf
  let expr ← normalizeLevelsExpr res.expr
  mkBackwardRuleFromExpr expr res.paramNames.toList

/-!
VC generation
-/

public structure VCGen.Context where
  specThms : SpecTheoremsNew
  /-- The backward rule for `SPred.entails_cons_intro`. -/
  entailsConsIntroRule : BackwardRule
  /-- The backward rule for `PostCond.entails.mk`. -/
  postCondEntailsMkRule : BackwardRule
  /-- The backward rule for `ExceptConds.entails.rfl`. -/
  exceptCondsEntailsRflRule : BackwardRule
  /-- The backward rule for `Triple.of_entails_wp`. -/
  tripleOfEntailsWPRule : BackwardRule

public structure VCGen.State where
  /--
  A cache mapping registered SpecThms to their backward rule to apply.
  The particular rule depends on the theorem name, the monad and the number of excess state
  arguments that the weakest precondition target is applied to.
  -/
  specBackwardRuleCache : Std.HashMap (Name × Expr × Nat) BackwardRule := {}
  /--
  A cache mapping matchers to their splitting backward rule to apply.
  The particular rule depends on the matcher name, the monad and the number of excess state
  arguments that the weakest precondition target is applied to.
  -/
  splitBackwardRuleCache : Std.HashMap (Name × Expr × Nat) BackwardRule := {}
  /--
  Holes of type `Invariant` that have been generated so far.
  -/
  invariants : Array MVarId := #[]
  /--
  The verification conditions that have been generated so far.
  -/
  vcs : Array MVarId := #[]

abbrev VCGenM := ReaderT VCGen.Context (StateRefT VCGen.State SymM)

namespace VCGen

@[inline]
meta def _root_.Std.HashMap.getDM [Monad m] [BEq α] [Hashable α]
    (cache : Std.HashMap α β) (key : α) (fallback : m β) : m (β × Std.HashMap α β) := do
  if let some b := cache.get? key then
    return (b, cache)
  let b ← fallback
  return (b, cache.insert key b)

meta def SpecTheoremNew.global? (specThm : SpecTheoremNew) : Option Name :=
  match specThm.proof with | .global decl => some decl | _ => none

/-- See the documentation for `mkBackwardRuleFromSpec` and `mkBackwardRuleFromSimpSpec`. -/
meta def mkBackwardRuleFromSpecCached (specThm : SpecTheoremNew) (m σs ps instWP : Expr)
    (excessArgs : Array Expr) : VCGenM BackwardRule := do
  let mkRuleSlow := match specThm.kind with
    | .triple _ => mkBackwardRuleFromSpec specThm m σs ps instWP excessArgs
    | .simp => mkBackwardRuleFromSimpSpec specThm m σs ps instWP excessArgs
  let s ← get
  let some decl := SpecTheoremNew.global? specThm | mkRuleSlow
  let (res, specBackwardRuleCache) ← s.specBackwardRuleCache.getDM (decl, m, excessArgs.size) mkRuleSlow
  set { s with specBackwardRuleCache }
  return res

open Lean.Elab.Tactic.Do in
/-- Creates and caches a backward rule for splitting `ite`, `dite`, or matchers. -/
meta def mkBackwardRuleFromSplitInfoCached (splitInfo : SplitInfo) (m σs ps instWP : Expr) (excessArgs : Array Expr) : _root_.VCGenM BackwardRule := do
  let cacheKey := match splitInfo with
    | .ite .. => ``ite
    | .dite .. => ``dite
    | .matcher matcherApp => matcherApp.matcherName
  let mkRuleSlow := mkBackwardRuleForSplit splitInfo m σs ps instWP excessArgs
  let s ← get
  let (res, splitBackwardRuleCache) ← s.splitBackwardRuleCache.getDM (cacheKey, m, excessArgs.size) mkRuleSlow
  set { s with splitBackwardRuleCache }
  return res

/--
Unfold `⦃P⦄ x ⦃Q⦄` into `P ⊢ₛ wp⟦x⟧ Q` by applying `Tiple.of_wp`, ensuring that `PostShape.args ps`
is reduced.
-/
meta def tripleOfWP (goal : MVarId) : _root_.VCGenM MVarId := goal.withContext do
  let .goals [goal] ← (← read).tripleOfEntailsWPRule.apply goal
    | throwError "Applying {.ofConstName ``Triple.of_entails_wp} to {goal} failed"
  goal.withContext do
    let target ← goal.getType
    let_expr ent@SPred.entails σs P Q := target | throwError "Expected SPred.entails: {target}"
    let σs ← shareCommonInc (← unfoldReducible σs)
    goal.replaceTargetDefEq (← Sym.Internal.mkAppS₃ ent σs P Q)

open Lean.Elab.Tactic.Do in
meta def decomposePostCondEntails (goal : MVarId) : _root_.VCGenM MVarId := goal.withContext do
  let target ← goal.getType
  let_expr PostCond.entails _ _ _ _ := target | return goal
  let .goals [goal₁, goal₂] ← (← read).postCondEntailsMkRule.apply goal
    | throwError "Applying {.ofConstName ``PostCond.entails} to {target} failed. It should not."
  goal₂.withContext do
    let target ← goal₂.getType
    let_expr ent@ExceptConds.entails ps P Q := target | throwError "invalid: {target}"
    let P := (← reduceProjBeta? P).getD P
    let Q := (← reduceProjBeta? Q).getD Q
    let P ← shareCommonInc P
    let Q ← shareCommonInc Q
    let goal₂ ← goal₂.replaceTargetDefEq (← Sym.Internal.mkAppS₃ ent ps P Q)
    let .goals [] ← (← read).exceptCondsEntailsRflRule.apply goal₂
      | throwError "Could not discharge {goal₂} by rfl. TODO: Implement this case."
  goal₁.withContext do
    let target ← goal₁.getType
    let .forallE x d b bi := target | throwError "Not a forall: {target}"
    let_expr ent@SPred.entails σs P Q := b | throwError "Not a SPred.entails: {target}"
    -- σs is of the form `PostShape.args ps` and we want to reduce it
    let σs ← shareCommonInc (← unfoldReducible σs)
    let b ← Sym.Internal.mkAppS₃ ent σs P Q
    let target ← Sym.Internal.MonadShareCommon.share1 <| .forallE x d b bi
    goal₁.replaceTargetDefEq target

/--
Reduces (1) Prod projection functions and (2) Projs in application heads,
and (3) beta reduces. Will not unfold projection functions unless further beta reduction happens.

It is a copy of `Lean.Elab.Tactic.Do.reduceProjBeta?` but for `SymM` that maintains maximal sharing.
-/
meta partial def reduceProjBeta? (e : Expr) : SymM (Option Expr) :=
  go none e.getAppFn e.getAppRevArgs
  where
    go lastReduction f rargs := do
      match f with
      | .mdata _ f => go lastReduction f rargs
      | .app f a => go lastReduction f (rargs.push a)
      | .lam .. =>
        if rargs.size = 0 then return lastReduction
        let e' := f.betaRev rargs
        let e' ← Sym.shareCommonInc e'
        go (some e') e'.getAppFn e'.getAppRevArgs
      | .const name .. =>
        let env ← getEnv
        match env.getProjectionStructureName? name with
        | some ``Prod => -- only reduce fst and snd for now
          match ← Meta.unfoldDefinition? (mkAppRev f rargs) with
          | some e' =>
            let e' ← Sym.shareCommonInc e'
            go lastReduction e'.getAppFn e'.getAppRevArgs
          | none => pure lastReduction
        | _ => pure lastReduction
      | .proj .. => match ← reduceProj? f with
        | some f' =>
          let e' := mkAppRev f' rargs
          let e' ← Sym.shareCommonInc e'
          go (some e') e'.getAppFn e'.getAppRevArgs
        | none    => pure lastReduction
      | .letE x ty val body nondep =>
        match ← go none body rargs with
        | none => pure lastReduction
        | some body' =>
          let body' ← Sym.shareCommonInc body'
          pure (some (.letE x ty val body' nondep))
      | _ => pure lastReduction

inductive SolveResult where
  /-- `target` was not of the form `H ⊢ₛ T`. -/
  | noEntailment (target : Expr)
  /-- The `T` in `H ⊢ₛ T` was not of the form `wp⟦e⟧ Q s₁ ... sₙ`. -/
  | noProgramFoundInTarget (T : Expr)
  /-- Don't know how to handle `e` in `H ⊢ₛ wp⟦e⟧ Q s₁ ... sₙ`. -/
  | noStrategyForProgram (e : Expr)
  /--
  Did not find a spec for the `e` in `H ⊢ₛ wp⟦e⟧ Q s₁ ... sₙ`.
  Candidates were `thms`, but none of them matched the monad.
  -/
  | noSpecFoundForProgram (e : Expr) (monad : Expr) (thms : Array SpecTheoremNew)
  /-- Successfully discharged the goal. These are the subgoals. -/
  | goals (subgoals : List MVarId)

open Sym Sym.Internal
-- The following function is vendored until it is made public:
/-- `mkAppRevRangeS f b e args == mkAppRev f (revArgs.extract b e)` -/
meta def mkAppRevRangeS [Monad m] [Internal.MonadShareCommon m] (f : Expr) (beginIdx endIdx : Nat) (revArgs : Array Expr) : m Expr :=
  loop revArgs beginIdx f endIdx
where
  loop (revArgs : Array Expr) (start : Nat) (b : Expr) (i : Nat) : m Expr := do
  if i ≤ start then
    return b
  else
    let i := i - 1
    loop revArgs start (← mkAppS b revArgs[i]!) i

open Sym Sym.Internal
meta def mkAppRevS [Monad m] [Internal.MonadShareCommon m] (f : Expr) (revArgs : Array Expr) : m Expr :=
  mkAppRevRangeS f 0 revArgs.size revArgs

open Sym Sym.Internal
meta def mkAppRangeS [Monad m] [Internal.MonadShareCommon m] (f : Expr) (beginIdx endIdx : Nat) (args : Array Expr) : m Expr :=
  loop args endIdx f beginIdx
where
  loop (args : Array Expr) (end' : Nat) (b : Expr) (i : Nat) : m Expr := do
  if end' ≤ i then
    return b
  else
    loop args end' (← mkAppS b args[i]!) (i + 1)

open Sym Sym.Internal
meta def mkAppNS [Monad m] [Internal.MonadShareCommon m] (f : Expr) (args : Array Expr) : m Expr :=
  mkAppRangeS f 0 args.size args

/--
The main VC generation function.
Looks at a goal of the form `P ⊢ₛ T`. Then
* If `T` is a lambda, introduce another state variable.
* If `T` is of the form `wp⟦e⟧ Q s₁ ... sₙ`, look up a spec theorem for `e`. Produce the backward
  rule to apply this spec theorem and then apply it ot the goal.
-/
meta def solve (goal : MVarId) : VCGenM SolveResult := goal.withContext do
  let target ← goal.getType
  trace[Elab.Tactic.Do.vcgen] "target: {target}"
  -- There are two layers of preprocessing before we get to taking apart program syntax.
  -- The first one is concerned with simplifying `target` until it is of the form `H ⊢ₛ T`.
  -- The second one is concerned with simplifying `H` and `T` such that none are head redexes
  -- and `T` is of the form `wp⟦e⟧ Q s₁ ... sₙ`.

  if target.isForall then
    let IntrosResult.goal _ goal ← Sym.intros goal | throwError "Failed to introduce binders for {target}"
    return .goals [goal]

  let f := target.getAppFn
  if f.isConstOf ``Triple then
    let goal ← tripleOfWP goal
    return .goals [goal]

  if f.isConstOf ``PostCond.entails then
    let goal ← decomposePostCondEntails goal
    return .goals [goal]

  let_expr ent@SPred.entails σs H T := target | return .noEntailment target
  -- The goal is of the form `H ⊢ₛ T`. Try some reductions to expose `wp⟦e⟧ Q s₁ ... sₙ` in `T`.

  if T.isLambda then
    -- This happens after applying the `get` spec. We have `T = (fun s => (wp⟦e⟧ Q, Q.snd).fst s s)`.
    -- Do what `mIntroForall` does, that is, eta-expand. Note that this introduces an
    -- extra state arg `s` to reduce away the lambda.
    let .goals [goal] ← (← read).entailsConsIntroRule.apply goal
      | throwError "Applying {.ofConstName ``SPred.entails_cons_intro} to {target} failed. It should not."
    return .goals [goal]

  /-
  Do a very targeted simplification to turn `H ⊢ₛ (fun _ => T, Q.snd).fst s` into `H ⊢ₛ T`, and
  similarly for `H`.
  This often arises as follows during backward reasoning (i.e., in precondition VCs):
  ```
    H ⊢ₛ wp⟦get >>= set⟧ Q
  = H ⊢ₛ wp⟦get⟧ (fun a => wp⟦set a⟧ Q, Q.snd)
  = H ⊢ₛ (fun s => (fun a => wp⟦set a⟧ Q, Q.snd).fst s s)
  = H s ⊢ₛ (fun a => wp⟦set a⟧ Q, Q.snd).fst s s
  -- This is where we simplify!
  = H s ⊢ₛ wp⟦set s⟧ Q s
  = H s ⊢ₛ Q.fst s s
  ```
  Furthermore, redexes in `H` occur in postcondition VCs.
  -/
  let H? ← reduceProjBeta? H
  let T? ← reduceProjBeta? T
  if H?.isSome || T?.isSome then
    let goal ← goal.replaceTargetDefEq (← Sym.Internal.mkAppS₃ ent σs (H?.getD H) (T?.getD T))
    return .goals [goal]

  -- Look for program syntax in `T`.
  T.withApp fun head args => do

  unless head.isConstOf ``PredTrans.apply do
    -- The target is not a predicate transformer. We assume there is no weakest precondition to
    -- discharge and try solving by (syntactic) rfl.
    if ← withAssignableSyntheticOpaque <| isDefEqS H T then
      trace[Elab.Tactic.Do.vcgen] "Solved by rfl {goal}"
      goal.assign (mkApp2 (mkConst ``SPred.entails.refl ent.constLevels!) σs H)
      return .goals []
    return .noProgramFoundInTarget T

  let wp := args[2]!
  let_expr wpConst@WP.wp m ps instWP α e := wp | return .noProgramFoundInTarget T
  -- `T` is of the form `wp⟦e⟧ Q s₁ ... sₙ`, where `e` is the program.
  -- We call `s₁ ... sₙ` the excess state args; the backward rules need to account for these.
  -- Excess state args are introduced by the spec of `get` (see lambda case above).
  let excessArgs := args.drop 4
  let f := e.getAppFn
  withTraceNode `Elab.Tactic.Do.vcgen (msg := fun _ => return m!"Program: {e}") do

  -- Zeta let-expressions
  if let .letE _x _ty val body _nonDep := f then
    let body' ← Sym.instantiateRevBetaS body #[val]
    let e' ← mkAppRevS body' e.getAppRevArgs
    let wp ← Sym.Internal.mkAppS₅ wpConst m ps instWP α e'
    let T ← mkAppNS head (args.set! 2 wp)
    let target ← mkAppS₃ ent σs H T
    let goal ← goal.replaceTargetDefEq target
    return .goals [goal]

  -- Split ite/dite/match
  if let some info ← liftMetaM <| Lean.Elab.Tactic.Do.getSplitInfo? e then
    let rule ← mkBackwardRuleFromSplitInfoCached info m σs ps instWP excessArgs
    let ApplyResult.goals goals ← rule.apply goal
      | throwError "Failed to apply split rule for {indentExpr e}"
    return .goals goals

  -- Apply registered specifications (both triple and simp specs use cached backward rules).
  if f.isConst || f.isFVar then
    trace[Elab.Tactic.Do.vcgen] "Applying a spec for {e}. Excess args: {excessArgs}"
    match ← (← read).specThms.findSpecs e with
    | .error thms => return .noSpecFoundForProgram e m thms
    | .ok thm =>
    trace[Elab.Tactic.Do.vcgen] "Spec for {e}: {thm.proof}"
    let rule ← mkBackwardRuleFromSpecCached thm m σs ps instWP excessArgs
    let ApplyResult.goals goals ← rule.apply goal
      | throwError "Failed to apply rule {thm.proof} for {indentExpr e}"
    return .goals goals

  return .noStrategyForProgram e

/--
Called when decomposing the goal further did not succeed; in this case we emit a VC for the goal.
-/
meta def emitVC (goal : MVarId) : VCGenM Unit := do
  let ty ← goal.getType
  goal.setKind .syntheticOpaque
  if ty.isAppOf ``Std.Do.Invariant then
    modify fun s => { s with invariants := s.invariants.push goal }
  else
    modify fun s => { s with vcs := s.vcs.push goal }

meta def work (goal : MVarId) : VCGenM Unit := do
  -- Normalize universe levels (one-time, cold path) so that backward rule pattern matching
  -- is structural. E.g., `max u v` and `max v u` get a canonical representation.
  let goal ← do
    let goal ← preprocessMVar goal
    let target ← goal.getType
    let target' ← normalizeLevelsExpr target
    if isSameExpr target target' then pure goal
    else liftMetaM <| goal.replaceTargetDefEq target'
  let mut worklist := Std.Queue.empty.enqueue goal
  -- while let some (goal, worklist') := worklist.dequeue? do
  repeat do
    let some (goal, worklist') := worklist.dequeue? | break
    worklist := worklist'
    let res ← solve goal
    match res with
    | .noEntailment .. | .noProgramFoundInTarget .. =>
      emitVC goal
    | .noSpecFoundForProgram prog _ #[] =>
      throwError "No spec found for program {prog}."
    | .noSpecFoundForProgram prog monad thms =>
      throwError "No spec matching the monad {monad} found for program {prog}. Candidates were {thms.map (·.proof)}."
    | .noStrategyForProgram prog =>
      throwError "Did not know how to decompose weakest precondition for {prog}"
    | .goals subgoals =>
      worklist := worklist.enqueueAll subgoals

public structure Result where
  invariants : Array MVarId
  vcs : Array MVarId

/--
Generate verification conditions for a goal of the form `P ⊢ₛ wp⟦e⟧ Q s₁ ... sₙ` by repeatedly
decomposing `e` using registered `@[spec]` theorems.
Return the VCs and invariant goals.
-/
public meta partial def main (goal : MVarId) (ctx : Context) : SymM Result := do
  let ((), state) ← StateRefT'.run (ReaderT.run (work goal) ctx) {}
  _ ← state.invariants.mapIdxM fun idx mv => do
    mv.setTag (Name.mkSimple ("inv" ++ toString (idx + 1)))
  _ ← state.vcs.mapIdxM fun idx mv => do
    mv.setTag (Name.mkSimple ("vc" ++ toString (idx + 1)) ++ (← mv.getTag).eraseMacroScopes)
  let invariants ← state.invariants.filterM (not <$> ·.isAssigned)
  let vcs ← state.vcs.filterM (not <$> ·.isAssigned)
  return { invariants, vcs }

/--
This function is best ignored; it's copied from `Lean.Elab.Tactic.Do.mkSpecContext`
and is more complex than necessary ATM.
-/
meta def mkSpecContext (lemmas : Syntax) (ignoreStarArg := false) : TacticM VCGen.Context := do
  let mut specThms ← getSpecTheorems
  let mut starArg := false
  for arg in lemmas[1].getSepArgs do
    if arg.getKind == ``simpErase then
      try
        let specThm ←
          if let some fvar ← Term.isLocalIdent? arg[1] then
            mkSpecTheoremFromLocal fvar.fvarId!
          else
            let id := arg[1]
            if let .ok declName ← observing (realizeGlobalConstNoOverloadWithInfo id) then
              mkSpecTheoremFromConst declName
            else
              withRef id <| throwUnknownConstant id.getId.eraseMacroScopes
        specThms := specThms.erase specThm.proof
      catch _ => pure () -- TODO: handle erasure of simp specs
    else if arg.getKind == ``simpLemma then
      unless arg[0].isNone && arg[1].isNone do
        throwError "← and ↑/↓ modifiers are not supported for spec lemmas"
      let term := arg[2]
      match ← Term.resolveId? term (withInfo := true) <|> Term.elabCDotFunctionAlias? ⟨term⟩ with
      | some (.const declName _) =>
        try
          let thm ← mkSpecTheoremFromConst declName
          specThms := specThms.insert thm
        catch _ =>
          -- TODO: handle user-provided simp specs
          throwError "Could not build spec theorem from {declName}"
      | some (.fvar fvar) =>
        try
          let thm ← mkSpecTheoremFromLocal fvar
          specThms := specThms.insert thm
        catch _ =>
          throwError "Could not build spec theorem from local {mkFVar fvar}"
      | _ => withRef term <| throwError "Could not resolve {repr term}"
    else if arg.getKind == ``simpStar then
      starArg := true
    else
      throwUnsupportedSyntax
  let simpThms ← getSpecSimpTheorems
  if starArg && !ignoreStarArg then
    let fvars ← getPropHyps
    for fvar in fvars do
      unless specThms.isErased (.local fvar) do
        try
          let thm ← mkSpecTheoremFromLocal fvar
          specThms := specThms.insert thm
        catch _ => continue
  let entailsConsIntroRule ← mkBackwardRuleFromDecl ``SPred.entails_cons_intro
  let postCondEntailsMkRule ← mkBackwardRuleFromDecl ``PostCond.entails.mk
  let exceptCondsEntailsRflRule ← mkBackwardRuleFromDecl ``ExceptConds.entails.rfl
  let tripleOfEntailsWPRule ← mkBackwardRuleFromDecl ``Triple.of_entails_wp
  let specThmsNew ← SymM.run <| migrateSpecTheoremsDatabase specThms simpThms
  return {
    specThms := specThmsNew,
    entailsConsIntroRule,
    postCondEntailsMkRule,
    exceptCondsEntailsRflRule,
    tripleOfEntailsWPRule,
  }

end VCGen

syntax (name := mvcgen') "mvcgen'"
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "] ")? : tactic

@[tactic mvcgen']
public meta def elabMVCGen' : Tactic := fun stx => withMainContext do
  let ctx ← VCGen.mkSpecContext stx[1]
  let goal ← getMainGoal
  let { invariants, vcs } ← SymM.run <| VCGen.main goal ctx
  replaceMainGoal (invariants ++ vcs).toList

/-!
Local tests for faster iteration:
-/

/-
def step (lim : Nat) : ExceptT String (StateM Nat) Unit := do
  let s ← get
  if s > lim then
    throw "s is too large"
  set (s + 1)

def loop (n : Nat) : ExceptT String (StateM Nat) Unit := do
  match n with
  | 0 => pure ()
  | n+1 => loop n; step n

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

-- set_option trace.Elab.Tactic.Do.vcgen true in
set_option trace.profiler true in
example : ⦃fun s => ⌜s = 0⌝⦄ loop 50 ⦃⇓_ s => ⌜s = 50⌝⦄ := by
  simp only [loop, step]
  mvcgen'
  -- all_goals grind
  all_goals sorry

set_option trace.Elab.Tactic.Do.vcgen true in
example :
  ⦃⌜True⌝⦄
  do
    let s ← get (m := ExceptT String (StateM Nat))
    if s > 20 then
      throw "s is too large"
    set (m := ExceptT String (StateM Nat)) (s + 1)
  ⦃post⟨fun _r s => ⌜s ≤ 21⌝, fun _err s => ⌜s > 20⌝⟩⦄ := by
  mvcgen' <;> grind
-/
