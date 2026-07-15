/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Lean
import Std.Internal
import Std.Tactic.Do

set_option mvcgen.warning false
set_option grind.warning false

/-!
# Tests for the `vcgen … frames` clause

A `frames` alternative attaches a state assertion `F` to a matched program whose registered spec is
*lossy* (drops a fact about state it does not touch). `vcgen` applies the framed spec, emits the
frame precondition and the `Frames` side goal, and recovers `F` in the postcondition.

The `Frames` side goal is established by `frames_mkFreshNat`, which reduces it through
`WP.Frames.of_wp_conjunctive` to a preservation triple `F ⊑ wp x (fun _ => F)` (using `WPConjunctive`
for the monad); `mkFreshNat` writes only `fst`, so it preserves any `snd`-fact.

The `recovers_*` proofs run at the `Id` base monad and register the `_Id` specializations of these
lemmas with `grind`. With the monad ground, `grind` derives a usable E-matching pattern, so the
discharge step `with finish` closes every VC, including the `Frames` side goal.
-/

open Lean Order Meta Elab Tactic Sym Std Internal.Do

abbrev AppState := Nat × Nat

@[irreducible] def mkFreshNat [Monad m] [MonadStateOf AppState m] : m Nat := do
  let n ← Prod.fst <$> get
  modify (fun s => (s.1 + 1, s.2))
  pure n

def mkFreshPair [Monad m] [MonadStateOf AppState m] : m (Nat × Nat) := do
  let a ← mkFreshNat
  let b ← mkFreshNat
  pure (a, b)

/-- Lossy spec: says nothing about `s.2`. -/
@[spec]
theorem mkFreshNat_spec_lossy [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
    ⦃ fun s => ⌜s.1 = n⌝ ⦄ (mkFreshNat : StateT AppState m Nat)
    ⦃ fun r s => ⌜r = n ∧ s.1 = n + 1⌝ ⦄ := by
  unfold mkFreshNat
  vcgen <;> simp_all

/-- `mkFreshNat` frames any `P` outside its `fst` footprint. The frame condition reduces through
`of_wp_conjunctive` to the preservation triple, which holds since `mkFreshNat` overwrites only `fst`. -/
theorem frames_mkFreshNat [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] [∀ β, WPConjunctive (m β) β Pred EPred] {P : AppState → Pred}
    (h : ∀ s a, P { s with fst := a } = P s) :
    WP.Frames (· ⊓ ·) (mkFreshNat : StateT AppState m Nat) P := by
  refine .of_wp_conjunctive (fun E => ?_)
  -- FIXME: use `vcgen [bumpSnd] with finish` here once the Pattern.match? level bug is fixed
  intro s
  unfold mkFreshNat
  simp only [StateT.wp_apply_eq, StateT.run_bind, StateT.run_get, StateT.run_modify,
    StateT.run_map, bind_pure_comp, map_pure]
  refine PartialOrder.rel_trans ?_
    (WPMonad.pure_le_wp_pure (m := m) (s.fst, s.fst + 1, s.snd) (fun x => P x.snd) E)
  show P s ⊑ P (s.fst + 1, s.snd)
  rw [h s (s.fst + 1)]

/-- `Id`-specialized `frames_mkFreshNat`. With the base monad ground, `grind` can derive a
usable pattern, so registering it lets `finish` discharge the preservation VC. -/
@[grind .]
theorem frames_mkFreshNat_Id [Assertion Pred] [Assertion EPred]
    [WPMonad Id Pred EPred] [∀ β, WPConjunctive (Id β) β Pred EPred] {P : AppState → Pred}
    (h : ∀ s a, P { s with fst := a } = P s) :
    WP.Frames (· ⊓ ·) (mkFreshNat : StateT AppState Id Nat) P :=
  frames_mkFreshNat h

/-- The frame recovers `s.2`, which the lossy spec dropped. The `fail_if_success` confirms the frame
is doing the work: without it, `grind` cannot close the lost `s.2 = 7`. -/
theorem recovers_snd [Assertion Pred] [Assertion EPred] [WPMonad Id Pred EPred]
    [∀ β, WPConjunctive (Id β) β Pred EPred] [∀ a : Pred, PreservesSup (meet a)] :
    ⦃ fun s => ⌜s.1 = 0 ∧ s.2 = 7⌝ ⦄ (mkFreshNat : StateT AppState Id Nat)
    ⦃ fun r s => ⌜r = 0 ∧ s.2 = 7⌝ ⦄ := by
  fail_if_success (vcgen <;> grind)
  vcgen frames | mkFreshNat => fun s => ⌜s.2 = 7⌝ with finish

/-- Two calls, two alternatives: consume-once frames each `mkFreshNat` exactly once. -/
theorem recovers_snd_pair [Assertion Pred] [Assertion EPred] [WPMonad Id Pred EPred]
    [∀ β, WPConjunctive (Id β) β Pred EPred] [∀ a : Pred, PreservesSup (meet a)] :
    ⦃ fun s => ⌜s.1 = 0 ∧ s.2 = 7⌝ ⦄ (mkFreshPair : StateT AppState Id (Nat × Nat))
    ⦃ fun p s => ⌜p.1 = 0 ∧ s.2 = 7⌝ ⦄ := by
  vcgen [mkFreshPair] frames
  | mkFreshNat => fun s => ⌜s.2 = 7⌝
  | mkFreshNat => fun s => ⌜s.2 = 7⌝
  with finish

/-! ## Complementary footprint: an operation that writes `snd` -/

@[irreducible] def mkFreshSnd [Monad m] [MonadStateOf AppState m] : m Nat := do
  let n ← Prod.snd <$> get
  modify (fun s => (s.1, s.2 + 1))
  pure n

/-- Lossy spec: says nothing about `s.1`. -/
@[spec]
theorem mkFreshSnd_spec_lossy [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
    ⦃ fun s => ⌜s.2 = o⌝ ⦄ (mkFreshSnd : StateT AppState m Nat)
    ⦃ fun r s => ⌜r = o ∧ s.2 = o + 1⌝ ⦄ := by
  unfold mkFreshSnd
  vcgen <;> simp_all

/-- `mkFreshSnd` frames any `P` outside its `snd` footprint. -/
theorem frames_mkFreshSnd [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] [∀ β, WPConjunctive (m β) β Pred EPred] {P : AppState → Pred}
    (h : ∀ s a, P { s with snd := a } = P s) :
    WP.Frames (· ⊓ ·) (mkFreshSnd : StateT AppState m Nat) P := by
  refine .of_wp_conjunctive (fun E => ?_)
  -- FIXME: use `vcgen [bumpSnd] with finish` here once the Pattern.match? level bug is fixed
  intro s
  unfold mkFreshSnd
  simp only [StateT.wp_apply_eq, StateT.run_bind, StateT.run_get, StateT.run_modify,
    StateT.run_map, bind_pure_comp, map_pure]
  refine PartialOrder.rel_trans ?_
    (WPMonad.pure_le_wp_pure (m := m) (s.snd, s.fst, s.snd + 1) (fun x => P x.snd) E)
  show P s ⊑ P (s.fst, s.snd + 1)
  rw [h s (s.snd + 1)]

/-- `Id`-specialized `frames_mkFreshSnd`, registered so `finish` discharges the preservation VC. -/
@[grind .]
theorem frames_mkFreshSnd_Id [Assertion Pred] [Assertion EPred]
    [WPMonad Id Pred EPred] [∀ β, WPConjunctive (Id β) β Pred EPred] {P : AppState → Pred}
    (h : ∀ s a, P { s with snd := a } = P s) :
    WP.Frames (· ⊓ ·) (mkFreshSnd : StateT AppState Id Nat) P :=
  frames_mkFreshSnd h

/-- Mirror of `recovers_snd`: frame the complementary (`fst`) footprint. -/
theorem recovers_fst [Assertion Pred] [Assertion EPred] [WPMonad Id Pred EPred]
    [∀ β, WPConjunctive (Id β) β Pred EPred] [∀ a : Pred, PreservesSup (meet a)] :
    ⦃ fun s => ⌜s.1 = 5 ∧ s.2 = 0⌝ ⦄ (mkFreshSnd : StateT AppState Id Nat)
    ⦃ fun r s => ⌜r = 0 ∧ s.1 = 5⌝ ⦄ := by
  fail_if_success (vcgen <;> grind)
  vcgen frames | mkFreshSnd => fun s => ⌜s.1 = 5⌝ with finish

/-! ## Two distinct framed operations in one program -/

def mkFreshMixed [Monad m] [MonadStateOf AppState m] : m (Nat × Nat) := do
  let a ← mkFreshNat
  let b ← mkFreshSnd
  pure (a, b)

/-- `mkFreshNat` (writes `fst`) and `mkFreshSnd` (writes `snd`) are framed by different alternatives:
each recovers the component the other op's lossy spec would drop. -/
theorem recovers_both [Assertion Pred] [Assertion EPred] [WPMonad Id Pred EPred]
    [∀ β, WPConjunctive (Id β) β Pred EPred] [∀ a : Pred, PreservesSup (meet a)] :
    ⦃ fun s => ⌜s.1 = 0 ∧ s.2 = 7⌝ ⦄ (mkFreshMixed : StateT AppState Id (Nat × Nat))
    ⦃ fun p s => ⌜s.1 = 1 ∧ s.2 = 8⌝ ⦄ := by
  vcgen [mkFreshMixed] frames
  | mkFreshNat => fun s => ⌜s.2 = 7⌝
  | mkFreshSnd => fun s => ⌜s.1 = 1⌝
  with finish

/-! ## Named pattern variable referenced by the frame -/

/-- `addFst k` writes `fst`, leaving `snd` untouched, and takes an explicit argument. -/
@[irreducible] def addFst (k : Nat) [Monad m] [MonadStateOf AppState m] : m Nat := do
  let n ← Prod.fst <$> get
  modify (fun s => (s.1 + k, s.2))
  pure n

/-- Lossy spec: says nothing about `s.2`. -/
@[spec]
theorem addFst_spec_lossy [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
    ⦃ fun s => ⌜s.1 = n⌝ ⦄ (addFst k : StateT AppState m Nat)
    ⦃ fun r s => ⌜r = n ∧ s.1 = n + k⌝ ⦄ := by
  unfold addFst
  vcgen <;> simp_all

/-- `addFst k` frames any `P` outside its `fst` footprint. -/
theorem frames_addFst [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] [∀ β, WPConjunctive (m β) β Pred EPred] {P : AppState → Pred} {k : Nat}
    (h : ∀ s a, P { s with fst := a } = P s) :
    WP.Frames (· ⊓ ·) (addFst k : StateT AppState m Nat) P := by
  refine .of_wp_conjunctive (fun E => ?_)
  -- FIXME: use `vcgen [bumpSnd] with finish` here once the Pattern.match? level bug is fixed
  intro s
  unfold addFst
  simp only [StateT.wp_apply_eq, StateT.run_bind, StateT.run_get, StateT.run_modify,
    StateT.run_map, bind_pure_comp, map_pure]
  refine PartialOrder.rel_trans ?_
    (WPMonad.pure_le_wp_pure (m := m) (s.fst, s.fst + k, s.snd) (fun x => P x.snd) E)
  show P s ⊑ P (s.fst + k, s.snd)
  rw [h s (s.fst + k)]

/-- `Id`-specialized `frames_addFst`, registered so `finish` discharges the preservation VC. -/
@[grind .]
theorem frames_addFst_Id [Assertion Pred] [Assertion EPred]
    [WPMonad Id Pred EPred] [∀ β, WPConjunctive (Id β) β Pred EPred] {P : AppState → Pred} {k : Nat}
    (h : ∀ s a, P { s with fst := a } = P s) :
    WP.Frames (· ⊓ ·) (addFst k : StateT AppState Id Nat) P :=
  frames_addFst h

/-- The frame `fun s => ⌜s.2 = j⌝` references the matched argument `j`, so `elabFrame` introduces
`let j := k` and the assignment is recovered in the postcondition. -/
theorem recovers_with_arg [Assertion Pred] [Assertion EPred] [WPMonad Id Pred EPred]
    [∀ β, WPConjunctive (Id β) β Pred EPred] [∀ a : Pred, PreservesSup (meet a)] :
    ⦃ fun s => ⌜s.1 = 0 ∧ s.2 = k⌝ ⦄ (addFst k : StateT AppState Id Nat)
    ⦃ fun r s => ⌜r = 0 ∧ s.2 = k⌝ ⦄ := by
  fail_if_success (vcgen <;> grind)
  vcgen frames | addFst j => fun s => ⌜s.2 = j⌝ with finish

/-! ## Polymorphic state type at a fixed universe -/

/-- Writes the `Nat` component of a `σ × Nat` state, for an abstract `σ : Type`. -/
@[irreducible] def bumpSnd {σ : Type} [Monad m] : StateT (σ × Nat) m Nat := do
  let n ← Prod.snd <$> get
  modify (fun s => (s.1, s.2 + 1))
  pure n

/-- Lossy spec: says nothing about `s.1`. -/
@[spec]
theorem bumpSnd_spec_lossy {σ : Type} [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] :
    ⦃ fun s => ⌜s.2 = o⌝ ⦄ (bumpSnd : StateT (σ × Nat) m Nat)
    ⦃ fun r s => ⌜r = o ∧ s.2 = o + 1⌝ ⦄ := by
  unfold bumpSnd
  vcgen <;> simp_all

/-- `bumpSnd` frames any `P` outside its `snd` footprint, over an abstract state `σ`. -/
theorem frames_bumpSnd {σ : Type} [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] [∀ β, WPConjunctive (m β) β Pred EPred] {P : σ × Nat → Pred}
    (h : ∀ s a, P { s with snd := a } = P s) :
    WP.Frames (· ⊓ ·) (bumpSnd : StateT (σ × Nat) m Nat) P := by
  refine .of_wp_conjunctive (fun E => ?_)
  -- FIXME: use `vcgen [bumpSnd] with finish` here once the Pattern.match? level bug is fixed
  intro s
  unfold bumpSnd
  simp only [StateT.wp_apply_eq, StateT.run_bind, StateT.run_get, StateT.run_modify,
    StateT.run_map, bind_pure_comp, map_pure]
  refine PartialOrder.rel_trans ?_
    (WPMonad.pure_le_wp_pure (m := m) (s.snd, s.fst, s.snd + 1) (fun x => P x.snd) E)
  show P s ⊑ P (s.fst, s.snd + 1)
  rw [h s (s.snd + 1)]

/-- `Id`-specialized `frames_bumpSnd` over an abstract state `σ`, registered so `finish`
discharges the preservation VC. -/
@[grind .]
theorem frames_bumpSnd_Id {σ : Type} [Assertion Pred] [Assertion EPred]
    [WPMonad Id Pred EPred] [∀ β, WPConjunctive (Id β) β Pred EPred] {P : σ × Nat → Pred}
    (h : ∀ s a, P { s with snd := a } = P s) :
    WP.Frames (· ⊓ ·) (bumpSnd : StateT (σ × Nat) Id Nat) P :=
  frames_bumpSnd h

/-- The frame recovers `s.1 = a` for an abstract `a : σ`, which the lossy spec dropped. -/
theorem recovers_fst_poly {σ : Type} [Assertion Pred] [Assertion EPred]
    [WPMonad Id Pred EPred] [∀ β, WPConjunctive (Id β) β Pred EPred] [∀ a : Pred, PreservesSup (meet a)] {a : σ} :
    ⦃ fun s => ⌜s.1 = a ∧ s.2 = 0⌝ ⦄ (bumpSnd : StateT (σ × Nat) Id Nat)
    ⦃ fun r s => ⌜r = 0 ∧ s.1 = a⌝ ⦄ := by
  fail_if_success (vcgen <;> grind)
  vcgen frames | bumpSnd => fun s => ⌜s.1 = a⌝ with finish

/-! ## Unmatched frame alternatives are rejected -/

-- A `frames` alternative whose program pattern matches no program in the goal is an error
-- (`mkFreshSnd` does not occur in the program).
/--
error: `frames` alternative matched no program in the goal
-/
#guard_msgs in
example [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [∀ β, WPConjunctive (m β) β Pred EPred] [∀ a : Pred, PreservesSup (meet a)] :
    ⦃ fun s => ⌜s.1 = 0 ∧ s.2 = 7⌝ ⦄ (mkFreshNat : StateT AppState m Nat)
    ⦃ fun r s => ⌜r = 0 ∧ s.2 = 7⌝ ⦄ := by
  vcgen frames | mkFreshSnd => fun s => ⌜s.2 = 7⌝

/-! ## The polymorphic frame lemmas instantiate at a concrete monad -/

example : ⦃ fun s => ⌜s.1 = 0 ∧ s.2 = 7⌝ ⦄ (mkFreshNat : StateM AppState Nat)
    ⦃ fun r s => ⌜r = 0 ∧ s.2 = 7⌝ ⦄ := recovers_snd
