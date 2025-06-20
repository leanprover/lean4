/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
prelude
import Std.Tactic.Do.Syntax
import Lean.Elab.Tactic.Do.ProofMode.MGoal
import Lean.Elab.Tactic.Do.ProofMode.Focus
import Lean.Elab.Tactic.Do.ProofMode.Basic
import Lean.Elab.Tactic.Do.ProofMode.Pure

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do
open Lean Elab Tactic Meta

initialize registerTraceClass `Meta.Tactic.Do.specialize

theorem Specialize.imp_stateful {P P' Q R : SPred σs}
  (hrefocus : P ∧ (Q → R) ⊣⊢ₛ P' ∧ Q) : P ∧ (Q → R) ⊢ₛ P ∧ R := by
  calc spred(P ∧ (Q → R))
    _ ⊢ₛ (P' ∧ Q) ∧ (Q → R) := SPred.and_intro hrefocus.mp SPred.and_elim_r
    _ ⊢ₛ P' ∧ Q ∧ (Q → R) := SPred.and_assoc.mp
    _ ⊢ₛ P' ∧ Q ∧ R := SPred.and_mono_r (SPred.and_intro SPred.and_elim_l SPred.imp_elim_r)
    _ ⊢ₛ (P' ∧ Q) ∧ R := SPred.and_assoc.mpr
    _ ⊢ₛ P ∧ R := SPred.and_mono_l (hrefocus.mpr.trans SPred.and_elim_l)

theorem Specialize.imp_pure {P Q R : SPred σs} [PropAsSPredTautology φ Q]
  (h : φ) : P ∧ (Q → R) ⊢ₛ P ∧ R := by
  calc spred(P ∧ (Q → R))
    _ ⊢ₛ P ∧ (Q ∧ (Q → R)) := SPred.and_mono_r (SPred.and_intro (SPred.true_intro.trans (PropAsSPredTautology.iff.mp h)) .rfl)
    _ ⊢ₛ P ∧ R := SPred.and_mono_r (SPred.mp SPred.and_elim_r SPred.and_elim_l)

theorem Specialize.forall {P : SPred σs} {ψ : α → SPred σs}
  (a : α) : P ∧ (∀ x, ψ x) ⊢ₛ P ∧ ψ a := SPred.and_mono_r (SPred.forall_elim a)

theorem Specialize.pure_start {φ : Prop} {H P T : SPred σs} [PropAsSPredTautology φ H] (hpure : φ) (hgoal : P ∧ H ⊢ₛ T) : P ⊢ₛ T :=
  (SPred.and_intro .rfl (SPred.true_intro.trans (PropAsSPredTautology.iff.mp hpure))).trans hgoal

theorem Specialize.pure_taut {σs} {φ} {P : SPred σs} [IsPure P φ] (h : φ) : ⊢ₛ P :=
  (SPred.pure_intro h).trans IsPure.to_pure.mpr

def mSpecializeImpStateful (σs : Expr) (P : Expr) (QR : Expr) (arg : TSyntax `term) : OptionT TacticM (Expr × Expr) := do
  guard (arg.raw.isIdent)
  let some argRes := focusHyp σs (mkAnd! σs P QR) arg.raw.getId | failure
  let some hyp := parseHyp? argRes.focusHyp | failure
  addHypInfo arg σs hyp
  OptionT.mk do -- no OptionT failure after this point
  -- The goal is P ∧ (Q → R)
  -- argRes.proof : P ∧ (Q → R) ⊣⊢ₛ P' ∧ Q
  -- we want to return (R, (proof : P ∧ (Q → R) ⊢ₛ P ∧ R))
  let some specHyp := parseHyp? QR | panic! "Precondition of specializeImpStateful violated"
  let P' := argRes.restHyps
  let Q := argRes.focusHyp
  let hrefocus := argRes.proof -- P ∧ (Q → R) ⊣⊢ₛ P' ∧ Q
  let mkApp3 (.const ``SPred.imp []) σs Q' R := specHyp.p | throwError "Expected implication {QR}"
  let proof := mkApp6 (mkConst ``Specialize.imp_stateful) σs P P' Q R hrefocus
  -- check proof
  trace[Meta.Tactic.Do.specialize] "Statefully specialize {specHyp.p} with {Q}. New Goal: {mkAnd! σs P R}"
  unless ← isDefEq Q Q' do
    throwError "failed to specialize {specHyp.p} with {Q}"

  return ({ specHyp with p := R }.toExpr, proof)

def mSpecializeImpPure (_σs : Expr) (P : Expr) (QR : Expr) (arg : TSyntax `term) : OptionT TacticM (Expr × Expr) := do
  let some specHyp := parseHyp? QR | panic! "Precondition of specializeImpPure violated"
  let mkApp3 (.const ``SPred.imp []) σs Q R := specHyp.p | failure
  let mut φ ← mkFreshExprMVar (mkSort .zero)
  let mut (hφ, mvarIds) ← try
    elabTermWithHoles arg.raw φ `specialize (allowNaturalHoles := true)
    catch _ => failure
  -- We might have hφ : φ and Q = ⌜φ⌝. In this case, convert hφ to a proof of ⊢ₛ ⌜φ⌝,
  -- so that we can infer an instance of `PropAsSPredTautology`.
  -- NB: PropAsSPredTautology φ ⌜φ⌝ is unfortunately impossible because ⊢ₛ ⌜φ⌝ does not imply φ.
  -- Hence this additional (lossy) conversion.
  if let some inst ← synthInstance? (mkApp3 (mkConst ``IsPure) σs Q φ) then
    hφ := mkApp5 (mkConst ``Specialize.pure_taut) σs φ Q inst hφ
    φ := mkApp2 (mkConst ``SPred.tautological) σs Q

  let some inst ← synthInstance? (mkApp3 (mkConst ``PropAsSPredTautology) φ σs Q)
    | failure

  OptionT.mk do -- no OptionT failure after this point
  -- The goal is P ∧ (Q → R)
  -- we want to return (R, (proof : P ∧ (Q → R) ⊢ₛ P ∧ R))
  pushGoals mvarIds
  let proof := mkApp7 (mkConst ``Specialize.imp_pure) σs φ P Q R inst hφ
  -- check proof
  trace[Meta.Tactic.Do.specialize] "Purely specialize {specHyp.p} with {Q}. New Goal: {mkAnd! σs P R}"
  -- logInfo m!"proof: {← inferType proof}"
  return ({ specHyp with p := R }.toExpr, proof)

def mSpecializeForall (_σs : Expr) (P : Expr) (Ψ : Expr) (arg : TSyntax `term) : OptionT TacticM (Expr × Expr) := do
  let some specHyp := parseHyp? Ψ | panic! "Precondition of specializeForall violated"
  let mkApp3 (.const ``SPred.forall [u]) α σs αR := specHyp.p | failure
  let (a, mvarIds) ← try
    elabTermWithHoles arg.raw α `specialize (allowNaturalHoles := true)
    catch _ => failure
  OptionT.mk do -- no OptionT failure after this point
  pushGoals mvarIds
  let proof := mkApp5 (mkConst ``Specialize.forall [u]) σs α P αR a
  let R := αR.beta #[a]
  -- check proof
  trace[Meta.Tactic.Do.specialize] "Instantiate {specHyp.p} with {a}. New Goal: {mkAnd! σs P R}"
  return ({ specHyp with p := R }.toExpr, proof)

theorem focus {P P' Q R : SPred σs} (hfocus : P ⊣⊢ₛ P' ∧ Q) (hnew : P' ∧ Q ⊢ₛ R) : P ⊢ₛ R :=
  hfocus.mp.trans hnew

@[builtin_tactic Lean.Parser.Tactic.mspecialize]
def elabMSpecialize : Tactic
  | `(tactic| mspecialize $hyp $args*) => do
  let (mvar, goal) ← mStartMVar (← getMainGoal)
  mvar.withContext do

  -- Want to prove goal P ⊢ T, where hyp occurs in P.
  -- So we
  -- 1. focus on hyp (referred to as H):  P ⊣⊢ₛ P' ∧ H. Prove P' ∧ H ⊢ₛ T
  -- 2. Produce a (transitive chain of) proofs
  --      P' ∧ H ⊢ P' ∧ H₁ ⊢ₛ P' ∧ H₂ ⊢ₛ ...
  --    One for each arg; end up with goal P' ∧ H' ⊢ₛ T
  -- 3. Recombine with mkAnd (NB: P' might be empty), compose with P' ∧ H' ⊣⊢ₛ mkAnd P' H'.
  -- 4. Make a new MVar for goal `mkAnd P' H' ⊢ T` and assign the transitive chain.
  let some specFocus := goal.focusHyp hyp.getId | throwError "unknown identifier '{hyp}'"
  let σs := goal.σs
  let P := specFocus.restHyps
  let mut H := specFocus.focusHyp
  let some hyp' := parseHyp? H | panic! "Invariant of specialize violated"
  addHypInfo hyp σs hyp'
  -- invariant: proof (_ : { goal with hyps := mkAnd! σs P H }.toExpr) fills the mvar
  let mut proof : Expr → Expr :=
    mkApp7 (mkConst ``focus) σs goal.hyps P H goal.target specFocus.proof

  for arg in args do
    let res? ← OptionT.run
      (mSpecializeImpStateful σs P H arg
        <|> mSpecializeImpPure σs P H arg
        <|> mSpecializeForall σs P H arg)
    match res? with
    | some (H', H2H') =>
      -- logInfo m!"H: {H}, proof: {← inferType H2H'}"
      proof := fun hgoal => proof (mkApp6 (mkConst ``SPred.entails.trans) σs (mkAnd! σs P H) (mkAnd! σs P H') goal.target H2H' hgoal)
      H := H'
    | none =>
      throwError "Could not specialize {H} with {arg}"

  let newMVar ← mkFreshExprSyntheticOpaqueMVar { goal with hyps := mkAnd! σs P H }.toExpr
  mvar.assign (proof newMVar)
  replaceMainGoal [newMVar.mvarId!]

  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.mspecializePure]
def elabMspecializePure : Tactic
  | `(tactic| mspecialize_pure $head $args* => $hyp) => do
  -- "mspecialize_pure" >> term >> many (ppSpace >> checkColGt "irrelevant" >> termParser (eval_prec max)) >> "as" >> ident
  let (mvar, goal) ← mStartMVar (← getMainGoal)
  mvar.withContext do

  -- Want to prove goal P ⊢ₛ T. `head` is a pure proof of type `φ` that turns into `⊢ₛ H` via `start_entails`.
  -- So we
  -- 1. Introduce `head` via `PropAsEntails` as stateful hypothesis named `hyp`, P ∧ (hyp : H) ⊢ₛ T
  -- 2. (from here on it's the same as `mspecialize`.)
  --    Produce a (transitive chain of) proofs
  --      P ∧ H ⊢ P ∧ H₁ ⊢ₛ P ∧ H₂ ⊢ₛ ...
  --    One for each arg; end up with goal P ∧ H' ⊢ₛ T
  -- 3. Recombine with mkAnd (NB: P' might be empty), compose with P' ∧ H' ⊣⊢ₛ mkAnd P' H'.
  -- 4. Make a new MVar for goal `mkAnd P' H' ⊢ T` and assign the transitive chain.
  let σs := goal.σs
  let P := goal.hyps
  let T := goal.target
  let hφ ← elabTerm head none
  let φ ← inferType hφ
  let H ← mkFreshExprMVar (mkApp (mkConst ``SPred) σs)
  let inst ← synthInstance (mkApp3 (mkConst ``PropAsSPredTautology) φ σs H)
  let uniq ← mkFreshId
  let mut H := (Hyp.mk hyp.getId uniq (← instantiateMVars H)).toExpr

  let goal : MGoal := { goal with hyps := mkAnd! σs P H }
  -- invariant: proof (_ : { goal with hyps := mkAnd! σs P H }.toExpr) fills the mvar
  let mut proof : Expr → Expr :=
    mkApp8 (mkConst ``Specialize.pure_start) σs φ H P T inst hφ

  for arg in args do
    let res? ← OptionT.run
      (mSpecializeImpStateful σs P H ⟨arg⟩
        <|> mSpecializeImpPure σs P H ⟨arg⟩
        <|> mSpecializeForall σs P H ⟨arg⟩)
    match res? with
    | some (H', H2H') =>
      -- logInfo m!"H: {H}, proof: {← inferType H2H'}"
      proof := fun hgoal => proof (mkApp6 (mkConst ``SPred.entails.trans) σs (mkAnd! σs P H) (mkAnd! σs P H') goal.target H2H' hgoal)
      H := H'
    | none =>
      throwError "Could not specialize {H} with {arg}"

  let some hyp' := parseHyp? H | panic! "Invariant of specialize_pure violated"
  addHypInfo hyp σs hyp'

  let newMVar ← mkFreshExprSyntheticOpaqueMVar { goal with hyps := mkAnd! σs P H }.toExpr
  mvar.assign (proof newMVar)
  replaceMainGoal [newMVar.mvarId!]
  | _ => throwUnsupportedSyntax
