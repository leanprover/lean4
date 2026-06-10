/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Tactic.Do.VCGen.Split
public import Lean.Elab.Tactic.Do.Internal.VCGen.Reduce
public import Lean.Elab.Tactic.Do.Internal.VCGen.SpecDB
public import Lean.Meta.Sym.AlphaShareBuilder
public import Lean.Meta.Sym.Apply
public import Lean.Meta.Sym.InstantiateMVarsS
public import Lean.Meta.Sym.Util
import Lean.Meta.WHNF

open Lean Meta Elab Tactic Sym
open Lean.Elab.Tactic.Do.SpecAttr
open Std.Do

namespace Lean.Elab.Tactic.Do.Internal

namespace VCGen

/-!
Construction of `BackwardRule`s from `SpecTheoremNew`s and split info. Pure
`SymM` — no knowledge of `VCGenM`. The `VCGenM` cache wrappers live in
`VCGen.RuleCache`.
-/

/-- Build goal: `P ⊢ₛ wp⟦prog⟧ Q ss...`. Meant to be partially applied for convenience. -/
private def mkGoal (u v : Level) (m σs ps instWP α : Expr) (ss : Array Expr) (P Q : Expr) (prog : Expr) : Expr :=
  mkApp3 (mkConst ``SPred.entails [u]) σs P
    (mkAppN (mkApp4 (mkConst ``PredTrans.apply [u]) ps α
      (mkApp5 (mkConst ``WP.wp [u, v]) m ps instWP α prog) Q) ss)

/-- Extract the program from a goal built by `mkGoal`. -/
private def extractProgFromGoal (goal : Expr) : Expr :=
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

#### Postcondition VCs

Similarly, a VC `hpost` is generated for the postcondition if it isn't schematic.
The details here are more complicated because we need to make available the pure facts in `P`
to prove `Q' ⊢ₚ Q`, so the `hpost` obligation becomes `P ⊢ₛ ⌜Q' ⊢ₚ Q⌝`.
For example, a hypothetical restrictive spec for `pure` in `Id` would be:
```
myPure.spec (n : Nat) : ⦃fun x => ⌜True⌝⦄ myPure n ⦃⇓ r x => ⌜r = n⌝⦄
```
This yields the following backward rule:
```
prf : ∀ (n : Nat) (P : Assertion .pure) (hpre : P ⊢ₛ ⌜True⌝)
  (Q : PostCond Nat .pure) (hpost : P ⊢ₛ ⌜(⇓ r => ⌜r = n⌝) ⊢ₚ Q⌝),
  P ⊢ₛ wp⟦myPure n⟧ Q
```

The `prf` term in this (most general) case is
```
fun n P hpre Q hpost =>
  SPred.pure_elim hpost fun h =>
    SPred.entails.trans (SPred.entails.trans hpre (myPure.spec n))
      (PredTrans.mono (wp (myPure n)) (⇓ r => ⌜r = n⌝) Q h)
```

#### Excess state arguments

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
`Std.Do` abbreviations, such as `Assertion ps` and `PostCond α ps`.
We do that by doing `unfoldReducible` on the forall telescope. The type for `StateM Nat` and one
excess state arg `s` becomes
```
prf : ∀ (α : Type) (x : StateT Nat Id α) (β : Type) (f : α → StateT Nat Id β)
        (Q : (β → Nat → ULift Prop) × ExceptConds (PostShape.arg Nat PostShape.pure)) (s : Nat)
        (P : ULift Prop) (hpre : P ⊢ₛ wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.snd) s),
        P ⊢ₛ wp⟦x >>= f⟧ Q s
```
We are still investigating how to get rid of more kernel unfolding overhead, such as for `wp` and
`List.rec`.
-/
public def mkBackwardRuleFromSpec (specThm : SpecTheoremNew) (m σs ps instWP : Expr) (excessArgs : Array Expr) : SymM BackwardRule := do
  let preprocessExpr : Expr → SymM Expr := shareCommon <=< liftMetaM ∘ unfoldReducible
  -- Create a backward rule for the spec we look up in the database.
  -- In order for the backward rule to apply, we need to instantiate both `m` and `ps` with the ones
  -- given by the use site.
  let (xs, _bs, spec, specTy) ← specThm.proof.instantiate
  let_expr f@Triple m' ps' instWP' α prog P Q := specTy
    | liftMetaM <| throwError "target not a Triple application {specTy}"
  -- Reject the spec and try the next if the monad doesn't match.
  -- `withDefault`: spec/goal instance projections (e.g. `WPMonad.toWP`)
  -- needs default to unfold; the ambient grind transparency is `reducible`.
  unless ← Meta.withDefault <| isDefEqGuarded m m' do
    throwError "Post program defeq Monad mismatch: {m} ≠ {m'}"
  unless ← Meta.withDefault <| isDefEqGuarded ps ps' do
    throwError "Post program defeq Postshape mismatch: {ps} ≠ {ps'}"
  unless ← Meta.withDefault <| isDefEqGuarded instWP instWP' do
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
    let Pss ← reduceHead <| mkAppN P ss  -- P s₁ ... sₙ
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
      -- Wrap PostCond.entails under the precondition frame: `P ⊢ₛ ⌜Q_spec ⊢ₚ Q'⌝`.
      -- This preserves pure precondition facts (e.g., `s = 42`) in the postcondition VC,
      -- which would otherwise be lost in a bare `PostCond.entails`.
      let framedEntailment (xs : Array Expr) := do
        let Q' := xs.back!
        let bare ← preprocessExpr <| mkApp4 (mkConst ``PostCond.entails [u]) α ps Q Q'
        let pureBare := mkApp2 (mkConst ``SPred.pure [u]) σs bare
        let frame := if needPreVC then xs[0]! else Pss
        preprocessExpr <| mkApp3 (mkConst ``SPred.entails [u]) σs frame pureBare
      declInfos := declInfos ++
                   #[(nmQ', .default, fun _ => pure typeQ),
                     (nmHPost, .default, framedEntailment)]
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
      prf := prf.beta ss -- Turn `⦃P⦄ prog ⦃Q⦄` into `P s₁ ... sₙ ⊢ₛ wp⟦prog⟧ Q s₁ ... sₙ`
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
        -- prf := pure_elim hpost (fun h => prf.trans <| (wp x).mono _ _ h)
        let wp := mkApp5 (mkConst ``WP.wp f.constLevels!) m ps instWP α prog
        let Q' := ys[ys.size-2]!
        let hpost := ys[ys.size-1]!
        let wpApplyQ' := mkApp4 (mkConst ``PredTrans.apply [u]) ps α wp Q' -- wp⟦prog⟧ Q'
        let wpApplyQ' := mkAppN wpApplyQ' ss -- wp⟦prog⟧ Q' s₁ ... sₙ
        -- Build `lambdaProof`: fun (h : Q ⊢ₚ Q') => entails.trans prf (mono wp Q Q' h ss)
        let phi ← preprocessExpr <| mkApp4 (mkConst ``PostCond.entails [u]) α ps Q Q'
        let hmono := mkApp6 (mkConst ``PredTrans.mono [u]) ps α wp Q Q' (mkBVar 0)
        let hmono := mkAppN hmono ss
        let innerPrf := mkApp6 (mkConst ``SPred.entails.trans [u]) σs newP wpApplyQ wpApplyQ' prf hmono
        let lambdaProof := mkLambda `h .default phi innerPrf
        prf := mkApp6 (mkConst ``SPred.pure_elim [u]) σs newP wpApplyQ' phi hpost lambdaProof
        newQ := Q'
        -- check prf
      return prf
  -- We use `mkBackwardRuleFromExpr` instead of `mkAuxLemma` + `mkBackwardRuleFromDecl` because
  -- the proof may contain free variables from the goal context (e.g., generic `m`, `ps`),
  -- which would cause `mkAuxLemma`'s `addDecl` to fail with a kernel error.
  let spec ← instantiateMVars spec
  let res ← abstractMVars spec
  mkBackwardRuleFromExpr res.expr res.paramNames.toList

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
public def mkBackwardRuleFromSimpSpec (specThm : SpecTheoremNew) (m σs ps instWP : Expr)
    (excessArgs : Array Expr) : SymM BackwardRule := do
  let preprocessExpr : Expr → SymM Expr := shareCommon <=< liftMetaM ∘ unfoldReducible
  let wpType ← liftMetaM <| Meta.inferType instWP
  let us := wpType.getAppFn.constLevels!
  let u := us[0]!
  let v := us[1]!
  let (xs, _, eqPrf, eqType) ← specThm.instantiate
  let_expr Eq eqα lhs rhs := eqType
    | liftMetaM <| throwError "simp spec is not an equation: {eqType}"
  let α ← mkFreshExprMVar (mkSort u.succ)
  unless ← isDefEqGuarded eqα (mkApp m α) do
    throwError "Simp spec: could not unify equation type {eqα} with {mkApp m α}"
  for x in xs do
    if x.isMVar && !(← x.mvarId!.isAssigned) then
      let xType ← Meta.inferType x
      try liftMetaM <| Meta.synthInstance xType >>= x.mvarId!.assign catch _ => pure ()
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
    let mα ← preprocessExpr (mkApp m α)
    let motiveBody := mkApp3 (mkConst ``SPred.entails [u]) σs P
      (mkAppN (mkApp4 (mkConst ``PredTrans.apply [u]) ps α
        (mkApp5 (mkConst ``WP.wp [u, v]) m ps instWP α (.bvar 0)) Q) ss)
    let motive := Expr.lam `prog mα motiveBody .default
    let eqProof ← liftMetaM <| Meta.mkCongrArg motive eqPrf
    let prf := mkApp4 (mkConst ``Eq.mpr [0]) conclusionType premiseType eqProof h
    liftMetaM <| mkLambdaFVars (#[Q] ++ ss ++ #[P, h]) prf
  let spec ← instantiateMVars spec
  let res ← abstractMVars spec
  mkBackwardRuleFromExpr res.expr res.paramNames.toList

open Lean.Elab.Tactic.Do in
/--
Creates a reusable backward rule for splitting `ite`, `dite`, or matchers.

Uses `SplitInfo.withAbstract` to open fvars for the split, then `SplitInfo.splitWith`
to build the splitting proof. Hypothesis types are discovered via `rwIfOrMatcher` inside
the splitter telescope.
-/
public def mkBackwardRuleForSplit (splitInfo : SplitInfo) (m σs ps instWP : Expr) (excessArgs : Array Expr) : SymM BackwardRule := do
  let preprocessExpr : Expr → SymM Expr := shareCommon <=< liftMetaM ∘ unfoldReducible
  let wpType ← liftMetaM <| Meta.inferType instWP
  let us := wpType.getAppFn.constLevels!
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
  mkBackwardRuleFromExpr res.expr res.paramNames.toList

end VCGen
end Lean.Elab.Tactic.Do.Internal
