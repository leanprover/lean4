import Std.Tactic.Do
open Std.Do

theorem mspec0 {α : Type u} [WP m ps]
    {x : m α}
    {P : Assertion ps} {P' : Assertion ps}
    {Q Q' : PostCond α ps}
    (h : Triple x P' Q') (hpre : P ⊢ₛ P') (hpost : Q' ⊢ₚ Q) : P ⊢ₛ wp⟦x⟧ Q := by
  apply SPred.entails.trans hpre
  apply SPred.entails.trans (Triple.iff.mp h)
  apply (wp x).mono _ _ hpost

macro "mspec'" e:term : tactic =>
  `(tactic|
      apply mspec0 $e _ _ <;>
        first | (exact SPred.entails.rfl) | (exact PostCond.entails.rfl) | skip)

theorem ex1 {n} :
    ⦃fun s => ⌜s = n⌝⦄ get (m := StateM Nat) ⦃⇓r => ⌜r = n⌝⦄ := by
  unfold Triple
  mspec' Spec.get_StateT
  simp

theorem ex2 {n} {m} {ps} [Monad m] [WPMonad m ps] :
    ⦃fun s => ⌜s = n⌝⦄ (get : StateT Nat m Nat) ⦃⇓r => ⌜r = n⌝⦄ := by
  unfold Triple
  mspec' Spec.get_StateT
  simp

macro "mspec'" "(" _x:ident ":=" m:term ")" e:term : tactic =>
  `(tactic|
      apply mspec0 (m := $m) $e _ _ <;>
        first | (exact SPred.entails.rfl) | (exact PostCond.entails.rfl) | skip)

-- set_option trace.Meta.isDefEq true in
theorem ex3 {n} {m} {ps} [Monad m] [WPMonad m ps] :
    ⦃fun s => ⌜s = n⌝⦄ (do let _ ← get; get : StateT Nat m Nat) ⦃⇓r => ⌜r = n⌝⦄ := by
  unfold Triple
  mspec' Spec.bind
  -- mspec' (m := StateT Nat m) Spec.bind
  mspec' Spec.get_StateT
  simp























namespace Ex4

def mkFreshNat {m} [Monad m] [MonadStateOf Nat m] : m Nat := do
  let n ← get
  modify (fun s => s + 1)
  pure n

set_option trace.Meta.isDefEq true in
theorem mkFreshNat_spec [Monad m] [WPMonad m ps] :
  ⦃fun p => ⌜p = n⌝⦄
  (mkFreshNat : StateT Nat m Nat)
  ⦃⇓ r p => ⌜r = n ∧ p = n + 1⌝⦄ := by
  unfold mkFreshNat Triple
  mspec' Spec.bind
  apply mspec0 Spec.get_StateT <;>
    first | (exact SPred.entails.rfl) | (exact PostCond.entails.rfl) | skip
  mintro _ ∀s
  dsimp only
  mspec
  mspec
  simp [*]
