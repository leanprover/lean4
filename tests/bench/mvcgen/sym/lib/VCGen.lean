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

-- Normally, we'd support the following two specs by unfolding:

@[spec]
theorem Spec.monadLift_trans [Monad o] [WPMonad o ps] [MonadLift n o] [MonadLiftT m n] (x : m α) :
    ⦃wp⟦MonadLift.monadLift (m := n) (n := o) (monadLift x)⟧ Q⦄ (MonadLiftT.monadLift x : o α) ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Spec.monadLift_refl [WP m ps] (x : m α) :
    ⦃wp⟦x⟧ Q⦄ (monadLift (n := m) x) ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Spec.MonadState_get_StateT {m ps} [Monad m] [WPMonad m ps] {σ} {Q : PostCond σ (.arg σ ps)} :
    ⦃fun s => Q.fst s s⦄ get (m := StateT σ m) ⦃Q⦄ := by
  simp only [Triple, WP.get_MonadState, WP.get_StateT, SPred.entails.refl]

@[spec]
theorem Spec.MonadState_get_ExceptT [Monad m] [MonadStateOf σ m] [WP m ps] :
    ⦃wp⟦monadLift (n := ExceptT ε m) (get : m σ)⟧ Q⦄ (get : ExceptT ε m σ) ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Spec.MonadState_get_ReaderT [Monad m] [MonadStateOf σ m] [WP m ps] :
    ⦃wp⟦monadLift (n := ReaderT ε m) (get : m σ)⟧ Q⦄ (get : ReaderT ε m σ) ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Spec.MonadStateOf_get_ExceptT [Monad m] [MonadStateOf σ m] [WP m ps] :
    ⦃wp⟦monadLift (n := ExceptT ε m) (get : m σ)⟧ Q⦄ (MonadStateOf.get : ExceptT ε m σ) ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Spec.MonadStateOf_get_ReaderT [Monad m] [MonadStateOf σ m] [WP m ps] :
    ⦃wp⟦monadLift (n := ReaderT ε m) (get : m σ)⟧ Q⦄ (MonadStateOf.get : ReaderT ε m σ) ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Spec.MonadStateOf_get_StateT_lift {m ps} [Monad m] [MonadStateOf σ m] [WP m ps] {Q : PostCond σ (.arg σ' ps)} :
    ⦃wp⟦monadLift (n := StateT σ' m) (get : m σ)⟧ Q⦄ (MonadStateOf.get (σ := σ) : StateT σ' m σ) ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Spec.MonadStateOf_set_ExceptT [Monad m] [MonadStateOf σ m] [WP m ps] {s : σ} :
    ⦃wp⟦monadLift (n := ExceptT ε m) (set (m := m) s)⟧ Q⦄ set (m := ExceptT ε m) s ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Spec.MonadStateOf_set_ReaderT [Monad m] [MonadStateOf σ m] [WP m ps] {s : σ} :
    ⦃wp⟦monadLift (n := ReaderT ε m) (set (m := m) s)⟧ Q⦄ set (m := ReaderT ε m) s ⦃Q⦄ := SPred.entails.rfl

@[spec]
theorem Spec.MonadStateOf_set_StateT_lift [Monad m] [MonadStateOf σ m] [WP m ps] {s : σ} :
    ⦃wp⟦monadLift (n := StateT σ' m) (set (m := m) s)⟧ Q⦄ set (m := StateT σ' m) s ⦃Q⦄ := SPred.entails.rfl

/-!
Creating backward rules for registered specifications
-/

namespace Lean.Elab.Tactic.Do.SpecAttr

public structure SpecTheoremNew where
  /--
  Pattern for the program expression.
  This is the key used in the discrimination tree.
  If the proof has type `∀ a b c, Triple prog P Q`, then the pattern is `prog[a:=#2, b:=#1, c:=#0]`.
  -/
  pattern : Sym.Pattern
  /-- The proof for the theorem. -/
  proof : SpecProof
  /--
  If `etaPotential` is non-zero, then the precondition contains meta variables that can be
  instantiated after applying `mintro ∀s` `etaPotential` many times.
  -/
  etaPotential : Nat := 0
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
  let type ← Sym.inferType expr
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
  return { pattern, proof, etaPotential, priority := prio }

meta def migrateSpecTheoremsDatabase (database : SpecTheorems) : SymM SpecTheoremsNew := do
  let mut specs : DiscrTree SpecTheoremNew := DiscrTree.empty
  for spec in database.specs.values do
    let newSpec ← mkSpecTheoremNew spec.proof spec.priority
    specs := Sym.insertPattern specs newSpec.pattern newSpec
  return { database with specs }

/--
Look up `SpecTheoremNew`s in the `@[spec]` database.
Takes all specs that match the given program `e` and sorts by descending priority.
-/
meta def SpecTheoremsNew.findSpecs (database : SpecTheoremsNew) (e : Expr) : SymM (Array SpecTheoremNew) := do
  let e ← instantiateMVars e
  let e ← shareCommon e
  let mut candidates := Sym.getMatch database.specs e
  candidates := candidates.filter fun spec => !database.erased.contains spec.proof
  if candidates.size > 1 then
    candidates ← candidates.filterM fun spec => do
      let res ← spec.pattern.match? e
      let some _ := res | return false
      -- let (_xs, _bs, _prf, type) ← spec.proof.instantiate
      -- let_expr Triple _m _ps _instWP _α prog _P _Q := type | throwError "Not a triple: {type}"
      -- isDefEqS e prog -- (← shareCommon (← unfoldReducible prog))
      return true
  return candidates.insertionSort fun s₁ s₂ => s₁.priority > s₂.priority

end Lean.Elab.Tactic.Do.SpecAttr

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
meta def mkBackwardRuleFromSpecs (specThms : Array SpecTheoremNew) (m σs ps instWP : Expr) (excessArgs : Array Expr) : SymM (Option (SpecTheoremNew × BackwardRule)) := do
  let preprocessExpr : Expr → SymM Expr := shareCommon <=< liftMetaM ∘ unfoldReducible
  for specThm in specThms do
    -- Create a backward rule for the spec we look up in the database.
    -- In order for the backward rule to apply, we need to instantiate both `m` and `ps` with the ones
    -- given by the use site.
    let (xs, _bs, spec, specTy) ← specThm.proof.instantiate
    let_expr f@Triple m' ps' instWP' α prog P Q := specTy
      | liftMetaM <| throwError "target not a Triple application {specTy}"
    -- Reject the spec and try the next if the monad doesn't match.
    unless ← isDefEqGuarded m m' do -- TODO: Try isDefEqS?
      continue
    unless ← isDefEqGuarded ps ps' do
      continue
    unless ← isDefEqGuarded instWP instWP' do
      continue

    -- We must ensure that P and Q are pattern variables so that the spec matches for every potential
    -- P and Q. We do so by introducing VCs accordingly.
    -- The following code could potentially be extracted into a definition at @[spec] attribute
    -- annotation time. That might help a bit with kernel checking time.
    let excessArgNamesTypes ← excessArgs.mapM fun arg =>
      return (← mkFreshUserName `s, ← Sym.inferType arg)
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
                       (nmHPre, .default, fun xs => entailment xs[0]!)]
      if needPostVC then
        let nmQ' ← mkFreshUserName `Q
        let nmHPost ← mkFreshUserName `hpost
        let entailment Q' := pure <| mkApp3 (mkConst ``PostCond.entails [u]) ps Q Q'
        declInfos := declInfos ++
                     #[(nmQ', .default, fun _ => pure typeQ),
                       (nmHPost, .default, fun xs => entailment xs[0]!)]
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
    let res ← abstractMVars spec
    let type ← preprocessExpr (← Sym.inferType res.expr)
    trace[Elab.Tactic.Do.vcgen] "Type of new auxiliary spec apply theorem: {type}"
    let spec ← Meta.mkAuxLemma res.paramNames.toList type res.expr
    return some (specThm, ← mkBackwardRuleFromDecl spec)
  return none

open Lean.Elab.Tactic.Do in
/--
Creates a reusable backward rule for `ite`. It proves a theorem of the following form:
```
example {m} {σ} {ps} [WP m (.arg σ ps)] -- These are fixed. The other arguments are parameters of the rule:
  {α} {c : Prop} [Decidable c] {t e : m α} {s : σ} {P : Assertion ps} {Q : PostCond α (.arg σ ps)}
  (hthen : P ⊢ₛ wp⟦t⟧ Q s) (helse : P ⊢ₛ wp⟦e⟧ Q s)
  : P ⊢ₛ wp⟦ite c t e⟧ Q s
```
-/
meta def mkBackwardRuleForIte (m σs ps instWP : Expr) (excessArgs : Array Expr) : SymM BackwardRule := do
  let preprocessExpr : Expr → SymM Expr := shareCommon <=< liftMetaM ∘ unfoldReducible
  let prf ← do
    let us := instWP.getAppFn.constLevels!
    let u := us[0]!
    let v := us[1]!
    withLocalDeclD `α (mkSort u.succ) fun α => do
    let mα ← preprocessExpr <| mkApp m α
    withLocalDeclD `c (mkSort 0) fun c => do
    withLocalDeclD `dec (mkApp (mkConst ``Decidable) c) fun dec => do
    withLocalDeclD `t mα fun t => do
    withLocalDeclD `e mα fun e => do
    let prog ← preprocessExpr (mkApp5 (mkConst ``ite [v.succ]) mα c dec t e)
    let excessArgNamesTypes ← excessArgs.mapM fun arg =>
      return (`s, ← Sym.inferType arg)
    withLocalDeclsDND excessArgNamesTypes fun ss => do
    withLocalDeclD `P (← preprocessExpr <| mkApp (mkConst ``SPred [u]) σs) fun P => do
    withLocalDeclD `Q (← preprocessExpr <| mkApp2 (mkConst ``PostCond [u]) α ps) fun Q => do
    let goalWithProg prog :=
      let wp := mkApp5 (mkConst ``WP.wp [u, v]) m ps instWP α prog
      let wpApplyQ := mkApp4 (mkConst ``PredTrans.apply [u]) ps α wp Q  -- wp⟦prog⟧ Q
      let wpApplyQ := mkAppN wpApplyQ ss  -- wp⟦prog⟧ Q s₁ ... sₙ
      mkApp3 (mkConst ``SPred.entails [u]) σs P wpApplyQ
    let thenType ← mkArrow c (goalWithProg t)
    withLocalDeclD `hthen (← preprocessExpr thenType) fun hthen => do
    let elseType ← mkArrow (mkNot c) (goalWithProg e)
    withLocalDeclD `helse (← preprocessExpr elseType) fun helse => do
    let onAlt (hc : Expr) (hcase : Expr) := do
      let res ← rwIfWith hc prog
      -- When `rw` fails, it returns `proof? := none`. We throw an error.
      if res.proof?.isNone then
        throwError "`rwIfWith` failed to rewrite {indentExpr e}."
      -- context = fun e => P ⊢ₛ wp⟦e⟧ Q s₁ ... sₙ
      let context ← withLocalDecl `e .default mα fun e => mkLambdaFVars #[e] (goalWithProg e)
      let res ← Simp.mkCongrArg context res
      res.mkEqMPR hcase
    let ht ← withLocalDecl `h .default c fun h => do mkLambdaFVars #[h] (← onAlt h (mkApp hthen h))
    let he ← withLocalDecl `h .default (mkNot c) fun h => do mkLambdaFVars #[h] (← onAlt h (mkApp helse h))
    let prf := mkApp5 (mkConst ``dite [0]) (goalWithProg prog) c dec ht he
    mkLambdaFVars (#[α, c, dec, t, e] ++ ss ++ #[P, Q, hthen, helse]) prf
  let res ← abstractMVars prf
  let type ← preprocessExpr (← Sym.inferType res.expr)
  let prf ← Meta.mkAuxLemma res.paramNames.toList type res.expr
  trace[Elab.Tactic.Do.vcgen] "Type of new auxiliary spec apply theorem for `ite`: {type}"
  mkBackwardRuleFromDecl prf

/-!
VC generation
-/

public structure VCGen.Context where
  specThms : SpecTheoremsNew
  /-- The backward rule for `SPred.entails_cons_intro`. -/
  entailsConsIntroRule : BackwardRule

public structure VCGen.State where
  /--
  A cache mapping registered SpecThms to their backward rule to apply.
  The particular rule depends on the theorem name, the monad and the number of excess state
  arguments that the weakest precondition target is applied to.
  -/
  specBackwardRuleCache : Std.HashMap (Array Name × Expr × Nat) (Option (SpecTheoremNew × BackwardRule)) := {}
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

/-- See the documentation for `SpecTheoremNew.mkBackwardRuleFromSpec` for more details. -/
meta def mkBackwardRuleFromSpecsCached (specThms : Array SpecTheoremNew) (m σs ps instWP : Expr) (excessArgs : Array Expr) : VCGenM (Option (SpecTheoremNew × BackwardRule)) := do
  let mkRuleSlow := mkBackwardRuleFromSpecs specThms m σs ps instWP excessArgs
  let s ← get
  let some decls := specThms.mapM SpecTheoremNew.global? | mkRuleSlow
  let (res, specBackwardRuleCache) ← s.specBackwardRuleCache.getDM (decls, m, excessArgs.size) mkRuleSlow
  set { s with specBackwardRuleCache }
  return res

open Lean.Elab.Tactic.Do in
/-- See the documentation for `SpecTheoremNew.mkBackwardRuleForIte` for more details. -/
meta def mkBackwardRuleFromSplitInfoCached (splitInfo : SplitInfo) (m σs ps instWP : Expr) (excessArgs : Array Expr) : _root_.VCGenM BackwardRule := do
  unless splitInfo matches .ite .. do throwError "Only `ite` is currently supported for splitting."
  let mkRuleSlow := mkBackwardRuleForIte m σs ps instWP excessArgs
  let s ← get
  let (res, splitBackwardRuleCache) ← s.splitBackwardRuleCache.getDM (``ite, m, excessArgs.size) mkRuleSlow
  set { s with splitBackwardRuleCache }
  return res

/-- Unfold `⦃P⦄ x ⦃Q⦄` into `P ⊢ₛ wp⟦x⟧ Q`. -/
meta def unfoldTriple (goal : MVarId) : SymM MVarId := goal.withContext do
  let type ← goal.getType
  unless type.isAppOf ``Triple do return goal
  let type ← unfoldDefinition type
  let goal ← goal.replaceTargetDefEq (← shareCommon type)
  preprocessMVar goal  -- need to reinstate subterm sharing

open Lean.Elab.Tactic.Do in
/--
Do a very targeted simplification to turn `P ⊢ₛ (fun _ => T, Q.snd).fst s` into `P ⊢ₛ T`.
This often arises as follows during backward reasoning:
```
  P ⊢ₛ wp⟦get >>= set⟧ Q
= P ⊢ₛ wp⟦get⟧ (fun a => wp⟦set a⟧ Q, Q.snd)
= P ⊢ₛ (fun s => (fun a => wp⟦set a⟧ Q, Q.snd).fst s s)
= P s ⊢ₛ (fun a => wp⟦set a⟧ Q, Q.snd).fst s s
-- This is where we simplify!
= P s ⊢ₛ wp⟦set s⟧ Q s
= P s ⊢ₛ Q.fst s s
-/
meta def simplifyTarget (goal : MVarId) : _root_.VCGenM MVarId := goal.withContext do
  let target ← goal.getType
  let_expr ent@SPred.entails σs P T := target | return goal
  let some T ← reduceProjBeta? T | return goal -- very slight simplification
  goal.replaceTargetDefEq (mkApp3 ent σs P T)

/--
Preprocess a goal, potentially closing it. This function assumes and preserves that the goal has is
normalized according to `Sym.preprocessMVar`.
-/
meta def preprocessGoal (goal : MVarId) : VCGenM (Option MVarId) := do
  let mut goal := goal
  if (← goal.getType).isForall then
    let IntrosResult.goal _ goal' ← Sym.intros goal | failure
    goal := goal'
  goal ← unfoldTriple goal
  goal ← simplifyTarget goal
  return goal

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
  let_expr ent@SPred.entails σs H T := target | return .noEntailment target
  -- The goal is of the form `H ⊢ₛ T`. Look for program syntax in `T`.

  if T.isLambda then
    -- This happens after applying the `get` spec. We have `T = (fun s => (wp⟦e⟧ Q, Q.snd).fst s s)`.
    -- Do what `mIntroForall` does, that is, eta-expand. Note that this introduces an
    -- extra state arg `s` to reduce away the lambda.
    let .goals goals ← (← read).entailsConsIntroRule.apply goal
      | throwError "Applying {.ofConstName ``SPred.entails_cons_intro} to {target} failed. It should not."
    return .goals goals

  T.withApp fun head args => do

  if head.isMVar then
    if ← withAssignableSyntheticOpaque <| isDefEq H T then -- TODO: Figure out why `isDefEqS` doesn't work here
      goal.assign (mkApp2 (mkConst ``SPred.entails.refl ent.constLevels!) σs H)
      return .goals []

  unless head.isConstOf ``PredTrans.apply do return .noProgramFoundInTarget T

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

  -- Hard-code match splitting for `ite` for now.
  if f.isAppOf ``ite then
    let some info ← Lean.Elab.Tactic.Do.getSplitInfo? e | return .noStrategyForProgram e
    let rule ← mkBackwardRuleFromSplitInfoCached info m σs ps instWP excessArgs
    let ApplyResult.goals goals ← rule.apply goal
      | throwError "Failed to apply split rule for {indentExpr e}"
    return .goals goals

  -- Apply registered specifications.
  if f.isConst || f.isFVar then
    trace[Elab.Tactic.Do.vcgen] "Applying a spec for {e}. Excess args: {excessArgs}"
    let thms ← (← read).specThms.findSpecs e
    trace[Elab.Tactic.Do.vcgen] "Candidates for {e}: {thms.map (·.proof)}"
    let some (thm, rule) ← mkBackwardRuleFromSpecsCached thms m σs ps instWP excessArgs
      | return .noSpecFoundForProgram e m thms
    trace[Elab.Tactic.Do.vcgen] "Applying rule {rule.pattern.pattern} at {target}"
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
  let mut worklist := Std.Queue.empty.enqueue (← preprocessMVar goal)
  -- while let some (goal, worklist') := worklist.dequeue? do
  repeat do
    let some (goal, worklist') := worklist.dequeue? | break
    worklist := worklist'
    let some goal ← preprocessGoal goal | continue
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
  for h : idx in [:state.invariants.size] do
    let mv := state.invariants[idx]
    mv.setTag (Name.mkSimple ("inv" ++ toString (idx + 1)))
  for h : idx in [:state.vcs.size] do
    let mv := state.vcs[idx]
    mv.setTag (Name.mkSimple ("vc" ++ toString (idx + 1)) ++ (← mv.getTag).eraseMacroScopes)
  return { invariants := state.invariants, vcs := state.vcs }

/--
This function is best ignored; it's copied from `Lean.Elab.Tactic.Do.mkSpecContext`
and is more complex than necessary ATM.
-/
meta def mkSpecContext (lemmas : Syntax) (ignoreStarArg := false) : TacticM VCGen.Context := do
  let mut specThms ← getSpecTheorems
  let mut simpStuff := #[]
  let mut starArg := false
  for arg in lemmas[1].getSepArgs do
    if arg.getKind == ``simpErase then
      try
        -- Try and build SpecTheorems for the lemma to erase to see if it's
        -- meant to be interpreted by SpecTheorems. Otherwise fall back to SimpTheorems.
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
      catch _ =>
        simpStuff := simpStuff.push ⟨arg⟩ -- simp tracks its own erase stuff
    else if arg.getKind == ``simpLemma then
      unless arg[0].isNone && arg[1].isNone do
        -- When there is ←, →, ↑ or ↓ then this is for simp
        simpStuff := simpStuff.push ⟨arg⟩
        continue
      let term := arg[2]
      match ← Term.resolveId? term (withInfo := true) <|> Term.elabCDotFunctionAlias? ⟨term⟩ with
      | some (.const declName _) =>
        let info ← getConstInfo declName
        try
          let thm ← mkSpecTheoremFromConst declName
          specThms := specThms.insert thm
        catch _ =>
          simpStuff := simpStuff.push ⟨arg⟩
      | some (.fvar fvar) =>
        let decl ← getFVarLocalDecl (.fvar fvar)
        try
          let thm ← mkSpecTheoremFromLocal fvar
          specThms := specThms.insert thm
        catch _ =>
          simpStuff := simpStuff.push ⟨arg⟩
      | _ => withRef term <| throwError "Could not resolve {repr term}"
    else if arg.getKind == ``simpStar then
      starArg := true
      simpStuff := simpStuff.push ⟨arg⟩
    else
      throwUnsupportedSyntax
  -- Build a mock simp call to build a simp context that corresponds to `simp [simpStuff]`
  let stx ← `(tactic| simp +unfoldPartialApp -zeta [$(Syntax.TSepArray.ofElems simpStuff),*])
  -- logInfo s!"{stx}"
  let res ← mkSimpContext stx.raw
    (eraseLocal := false)
    (simpTheorems := getSpecSimpTheorems)
    (ignoreStarArg := ignoreStarArg)
  -- trace[Elab.Tactic.Do.vcgen] "{res.ctx.simpTheorems.map (·.toUnfold.toList)}"
  if starArg && !ignoreStarArg then
    let fvars ← getPropHyps
    for fvar in fvars do
      unless specThms.isErased (.local fvar) do
        try
          let thm ← mkSpecTheoremFromLocal fvar
          specThms := specThms.insert thm
        catch _ => continue
  let entailsConsIntroRule ← mkBackwardRuleFromDecl ``SPred.entails_cons_intro
  let specThmsNew ← SymM.run <| migrateSpecTheoremsDatabase specThms
  return { specThms := specThmsNew, entailsConsIntroRule }

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
