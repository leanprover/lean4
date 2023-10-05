/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core
import Init.NotationExtra

universe u v

/-! # Classical reasoning support -/

namespace Classical

noncomputable def indefiniteDescription {α : Sort u} (p : α → Prop) (h : ∃ x, p x) : {x // p x} :=
  choice <| let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩

noncomputable def choose {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α :=
  (indefiniteDescription p h).val

theorem choose_spec {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : p (choose h) :=
  (indefiniteDescription p h).property

/-- Diaconescu's theorem: excluded middle from choice, Function extensionality and propositional extensionality. -/
theorem em (p : Prop) : p ∨ ¬p :=
  -- Divide `Bool` by `p`
  let A := Quotient ⟨
    fun x y => x = y ∨ p,
    fun _ => Or.inl rfl,
    fun
      | Or.inl hxy => Or.inl (Eq.symm hxy)
      | Or.inr hp => Or.inr hp,
    fun
      | Or.inl hxy, Or.inl hyz => Or.inl (Eq.trans hxy hyz)
      | Or.inr hp, _ => Or.inr hp
      | _, Or.inr hp => Or.inr hp
  ⟩

  -- Choose a section `σ : A → Bool` of the projection `π : Bool → A`
  let π : Bool → A := Quotient.mk _
  let σ : A → Bool := fun a => Classical.choose (Quotient.exists_rep a)
  have σ_section (a : A) : π (σ a) = a := Classical.choose_spec (Quotient.exists_rep a)
  have σ_injective {x y : A} (e : σ x = σ y) : x = y := σ_section x ▸ σ_section y ▸ congrArg π e

  -- Whether `P` is true matches whether `σ (π true) = σ (π false)`, which is decidable
  if h : σ (π true) = σ (π false) then
    Or.inl (match Quotient.exact (σ_injective h) with | Or.inr b => b)
  else
    Or.inr (fun hp => h (congrArg σ (Quotient.sound (Or.inr hp))))

theorem exists_true_of_nonempty {α : Sort u} : Nonempty α → ∃ _ : α, True
  | ⟨x⟩ => ⟨x, trivial⟩

noncomputable def inhabited_of_nonempty {α : Sort u} (h : Nonempty α) : Inhabited α :=
  ⟨choice h⟩

noncomputable def inhabited_of_exists {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : Inhabited α :=
  inhabited_of_nonempty (Exists.elim h (fun w _ => ⟨w⟩))

/-- All propositions are `Decidable`. -/
noncomputable scoped instance (priority := low) propDecidable (a : Prop) : Decidable a :=
  choice <| match em a with
    | Or.inl h => ⟨isTrue h⟩
    | Or.inr h => ⟨isFalse h⟩

noncomputable def decidableInhabited (a : Prop) : Inhabited (Decidable a) where
  default := inferInstance

noncomputable def typeDecidableEq (α : Sort u) : DecidableEq α :=
  fun _ _ => inferInstance

noncomputable def typeDecidable (α : Sort u) : PSum α (α → False) :=
  match (propDecidable (Nonempty α)) with
  | (isTrue hp)  => PSum.inl (@default _ (inhabited_of_nonempty hp))
  | (isFalse hn) => PSum.inr (fun a => absurd (Nonempty.intro a) hn)

noncomputable def strongIndefiniteDescription {α : Sort u} (p : α → Prop) (h : Nonempty α) : {x : α // (∃ y : α, p y) → p x} :=
  @dite _ (∃ x : α, p x) (propDecidable _)
    (fun (hp : ∃ x : α, p x) =>
      show {x : α // (∃ y : α, p y) → p x} from
      let xp := indefiniteDescription _ hp;
      ⟨xp.val, fun _ => xp.property⟩)
    (fun hp => ⟨choice h, fun h => absurd h hp⟩)

/-- the Hilbert epsilon Function -/
noncomputable def epsilon {α : Sort u} [h : Nonempty α] (p : α → Prop) : α :=
  (strongIndefiniteDescription p h).val

theorem epsilon_spec_aux {α : Sort u} (h : Nonempty α) (p : α → Prop) : (∃ y, p y) → p (@epsilon α h p) :=
  (strongIndefiniteDescription p h).property

theorem epsilon_spec {α : Sort u} {p : α → Prop} (hex : ∃ y, p y) : p (@epsilon α (nonempty_of_exists hex) p) :=
  epsilon_spec_aux (nonempty_of_exists hex) p hex

theorem epsilon_singleton {α : Sort u} (x : α) : @epsilon α ⟨x⟩ (fun y => y = x) = x :=
  @epsilon_spec α (fun y => y = x) ⟨x, rfl⟩

/-- the axiom of choice -/
theorem axiomOfChoice {α : Sort u} {β : α → Sort v} {r : ∀ x, β x → Prop} (h : ∀ x, ∃ y, r x y) : ∃ (f : ∀ x, β x), ∀ x, r x (f x) :=
  ⟨_, fun x => choose_spec (h x)⟩

theorem skolem {α : Sort u} {b : α → Sort v} {p : ∀ x, b x → Prop} : (∀ x, ∃ y, p x y) ↔ ∃ (f : ∀ x, b x), ∀ x, p x (f x) :=
  ⟨axiomOfChoice, fun ⟨f, hw⟩ (x) => ⟨f x, hw x⟩⟩

theorem propComplete (a : Prop) : a = True ∨ a = False :=
  match em a with
  | Or.inl ha => Or.inl (propext (Iff.intro (fun _ => ⟨⟩) (fun _ => ha)))
  | Or.inr hn => Or.inr (propext (Iff.intro (fun h => hn h) (fun h => False.elim h)))

-- this supercedes byCases in Decidable
theorem byCases {p q : Prop} (hpq : p → q) (hnpq : ¬p → q) : q :=
  Decidable.byCases (dec := propDecidable _) hpq hnpq

-- this supercedes byContradiction in Decidable
theorem byContradiction {p : Prop} (h : ¬p → False) : p :=
  Decidable.byContradiction (dec := propDecidable _) h

/--
`by_cases (h :)? p` splits the main goal into two cases, assuming `h : p` in the first branch, and `h : ¬ p` in the second branch.
-/
syntax "by_cases " (atomic(ident " : "))? term : tactic

macro_rules
  | `(tactic| by_cases $h : $e) =>
    `(tactic|
      cases em $e with
      | inl $h => _
      | inr $h => _)
  | `(tactic| by_cases $e) =>
    `(tactic|
      cases em $e with
      | inl h => _
      | inr h => _)

end Classical
