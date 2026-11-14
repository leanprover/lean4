import Std.WP

/-!
# `vcgen` over a partial order of assertions

A `WP` interpretation is monotone for a partial order of assertions (`WP.IsMonotone`). This test gives a small command
language `Cmd σ O` the assertions `σ → O` for an arbitrary partial order `O`. Quantitative program
logics have assertions of this kind: the assertions of a quantum program map classical stores to
quantum effects, and the Löwner order on effects is a partial order but not a lattice. `vcgen`
reduces a triple of `Cmd σ O` to verification conditions in `O`.
-/

open Std.WP Lean.Order

set_option experimental.vcgen true

/-- A command over states `σ`. The type of a program determines the type of its assertions, so
`Cmd σ O` carries the type `O` that assertions take values in. -/
inductive Cmd (σ O : Type) where
  | skip
  | assign (f : σ → σ)
  | seq (c₁ c₂ : Cmd σ O)

variable {σ O : Type} [PartialOrder O]

/-- The weakest precondition of a command for a postcondition. -/
def Cmd.wpo : Cmd σ O → (σ → O) → σ → O
  | .skip, Q => Q
  | .assign f, Q => fun s => Q (f s)
  | .seq c₁ c₂, Q => c₁.wpo (c₂.wpo Q)

theorem Cmd.wpo_mono (c : Cmd σ O) {Q Q' : σ → O} (h : Q ⊑ Q') : c.wpo Q ⊑ c.wpo Q' := by
  induction c generalizing Q Q' with
  | skip => exact h
  | assign f => exact fun s => h (f s)
  | seq c₁ c₂ ih₁ ih₂ => exact ih₁ (ih₂ h)

instance : WP (Cmd σ O) Unit (σ → O) EStack⟨⟩ where
  trans c := ⟨fun Q _ => c.wpo (Q ())⟩

instance : WP.IsMonotone (Cmd σ O) := fun c => ⟨fun _ _ _ _ _ hQ => c.wpo_mono (hQ ())⟩

variable {Q : Unit → σ → O} {E : EStack⟨⟩}

@[spec] theorem Spec.skip : Triple (Cmd.skip : Cmd σ O) (Q ()) Q E :=
  ⟨PartialOrder.rel_refl⟩

@[spec] theorem Spec.assign (f : σ → σ) :
    Triple (Cmd.assign f : Cmd σ O) (fun s => Q () (f s)) Q E :=
  ⟨PartialOrder.rel_refl⟩

@[spec] theorem Spec.seq (c₁ c₂ : Cmd σ O) :
    Triple (Cmd.seq c₁ c₂) (wp c₁ (fun _ => wp c₂ Q E) E) Q E :=
  ⟨PartialOrder.rel_refl⟩

/-- `swap` exchanges the two components of a state through a third one. -/
def swap : Cmd (Nat × Nat × Nat) O :=
  .seq (.assign fun (x, y, _) => (x, y, x))
    (.seq (.assign fun (_, y, t) => (y, y, t)) (.assign fun (x, _, t) => (x, t, t)))

/-- `vcgen` pushes the postcondition through the three assignments of `swap`. The verification
condition compares the precondition with the postcondition at the swapped state, in `O`. -/
example (P : Nat × Nat × Nat → O) (post : Nat → Nat → O)
    (h : ∀ x y t, P (x, y, t) ⊑ post y x) :
    Triple (swap (O := O)) P (fun _ s => post s.1 s.2.1) E := by
  vcgen [swap]
  exact h _ _ _
