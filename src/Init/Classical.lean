/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude
import Init.PropLemmas

universe u v

/-! # Classical reasoning support -/

namespace Classical

noncomputable def indefiniteDescription {α : Sort u} (p : α → Prop) (h : ∃ x, p x) : {x // p x} :=
  choice <| let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩

/--
Given that there exists an element satisfying `p`, returns one such element.

This is a straightforward consequence of, and equivalent to, `Classical.choice`.

See also `choose_spec`, which asserts that the returned value has property `p`.
-/
noncomputable def choose {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α :=
  (indefiniteDescription p h).val

theorem choose_spec {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : p (choose h) :=
  (indefiniteDescription p h).property

/-- **Diaconescu's theorem**: excluded middle from choice, Function extensionality and propositional extensionality. -/
theorem em (p : Prop) : p ∨ ¬p :=
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p
  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
  let u : Prop := choose exU
  let v : Prop := choose exV
  have u_def : U u := choose_spec exU
  have v_def : V v := choose_spec exV
  have not_uv_or_p : u ≠ v ∨ p :=
    match u_def, v_def with
    | Or.inr h, _ => Or.inr h
    | _, Or.inr h => Or.inr h
    | Or.inl hut, Or.inl hvf =>
      have hne : u ≠ v := by simp [hvf, hut, true_ne_false]
      Or.inl hne
  have p_implies_uv : p → u = v :=
    fun hp =>
    have hpred : U = V :=
      funext fun x =>
        have hl : (x = True ∨ p) → (x = False ∨ p) :=
          fun _ => Or.inr hp
        have hr : (x = False ∨ p) → (x = True ∨ p) :=
          fun _ => Or.inr hp
        show (x = True ∨ p) = (x = False ∨ p) from
          propext (Iff.intro hl hr)
    have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV := by
      rw [hpred]; intros; rfl
    show u = v from h₀ _ _
  match not_uv_or_p with
  | Or.inl hne => Or.inr (mt p_implies_uv hne)
  | Or.inr h   => Or.inl h

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

instance (a : Prop) : Nonempty (Decidable a) := ⟨propDecidable a⟩

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
  | Or.inl ha => Or.inl (eq_true ha)
  | Or.inr hn => Or.inr (eq_false hn)

-- this supersedes byCases in Decidable
theorem byCases {p q : Prop} (hpq : p → q) (hnpq : ¬p → q) : q :=
  Decidable.byCases (dec := propDecidable _) hpq hnpq

-- this supersedes byContradiction in Decidable
theorem byContradiction {p : Prop} (h : ¬p → False) : p :=
  Decidable.byContradiction (dec := propDecidable _) h

/-- The Double Negation Theorem: `¬¬P` is equivalent to `P`.
The left-to-right direction, double negation elimination (DNE),
is classically true but not constructively. -/
@[simp] theorem not_not : ¬¬a ↔ a := Decidable.not_not

/-- Transfer decidability of `¬ p` to decidability of `p`. -/
-- This can not be an instance as it would be tried everywhere.
def decidable_of_decidable_not (p : Prop) [h : Decidable (¬ p)] : Decidable p :=
  match h with
  | isFalse h => isTrue (Classical.not_not.mp h)
  | isTrue h => isFalse h

attribute [local instance] decidable_of_decidable_not in
/-- Negation of the condition `P : Prop` in a `dite` is the same as swapping the branches. -/
@[simp low] protected theorem dite_not [hn : Decidable (¬p)] (x : ¬p → α) (y : ¬¬p → α) :
    dite (¬p) x y = dite p (fun h => y (not_not_intro h)) x := by
  cases hn <;> rename_i g
  · simp [not_not.mp g]
  · simp [g]

attribute [local instance] decidable_of_decidable_not in
/-- Negation of the condition `P : Prop` in a `ite` is the same as swapping the branches. -/
@[simp low] protected theorem ite_not (p : Prop) [Decidable (¬ p)] (x y : α) : ite (¬p) x y = ite p y x :=
  dite_not (fun _ => x) (fun _ => y)

attribute [local instance] decidable_of_decidable_not in
@[simp low] protected theorem decide_not (p : Prop) [Decidable (¬ p)] : decide (¬p) = !decide p :=
  byCases (fun h : p => by simp_all) (fun h => by simp_all)

@[simp low] theorem not_forall {p : α → Prop} : (¬∀ x, p x) ↔ ∃ x, ¬p x := Decidable.not_forall

theorem not_forall_not {p : α → Prop} : (¬∀ x, ¬p x) ↔ ∃ x, p x := Decidable.not_forall_not
theorem not_exists_not {p : α → Prop} : (¬∃ x, ¬p x) ↔ ∀ x, p x := Decidable.not_exists_not

theorem forall_or_exists_not (P : α → Prop) : (∀ a, P a) ∨ ∃ a, ¬ P a := by
  rw [← not_forall]; exact em _
theorem exists_or_forall_not (P : α → Prop) : (∃ a, P a) ∨ ∀ a, ¬ P a := by
  rw [← not_exists]; exact em _

theorem or_iff_not_imp_left  : a ∨ b ↔ (¬a → b) := Decidable.or_iff_not_imp_left
theorem or_iff_not_imp_right : a ∨ b ↔ (¬b → a) := Decidable.or_iff_not_imp_right

theorem not_imp_iff_and_not : ¬(a → b) ↔ a ∧ ¬b := Decidable.not_imp_iff_and_not

theorem not_and_iff_or_not_not : ¬(a ∧ b) ↔ ¬a ∨ ¬b := Decidable.not_and_iff_or_not_not

theorem not_iff : ¬(a ↔ b) ↔ (¬a ↔ b) := Decidable.not_iff

@[simp] theorem imp_iff_left_iff  : (b ↔ a → b) ↔ a ∨ b := Decidable.imp_iff_left_iff
@[simp] theorem imp_iff_right_iff : (a → b ↔ b) ↔ a ∨ b := Decidable.imp_iff_right_iff

@[simp] theorem and_or_imp : a ∧ b ∨ (a → c) ↔ a → b ∨ c := Decidable.and_or_imp

@[simp] theorem not_imp : ¬(a → b) ↔ a ∧ ¬b := Decidable.not_imp_iff_and_not

@[simp] theorem imp_and_neg_imp_iff (p : Prop) {q : Prop} : (p → q) ∧ (¬p → q) ↔ q :=
  Iff.intro (fun (a : _ ∧ _) => (Classical.em p).rec a.left a.right)
            (fun a => And.intro (fun _ => a) (fun _ => a))

end Classical

/- Export for Mathlib compat. -/
export Classical (imp_iff_right_iff imp_and_neg_imp_iff and_or_imp not_imp)

/-- Extract an element from an existential statement, using `Classical.choose`. -/
-- This enables projection notation.
@[reducible] noncomputable def Exists.choose {p : α → Prop} (P : ∃ a, p a) : α := Classical.choose P

/-- Show that an element extracted from `P : ∃ a, p a` using `P.choose` satisfies `p`. -/
theorem Exists.choose_spec {p : α → Prop} (P : ∃ a, p a) : p P.choose := Classical.choose_spec P
