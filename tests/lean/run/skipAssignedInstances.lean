@[reducible]
def swap {φ : α → β → Sort u₃} (f : ∀ x y, φ x y) : ∀ y x, φ x y := fun y x => f x y

theorem forall_swap {p : α → β → Prop} : (∀ x y, p x y) ↔ ∀ y x, p x y := ⟨swap, swap⟩

@[simp]
theorem nonempty_Prop {p : Prop} : Nonempty p ↔ p :=
  Iff.intro (fun ⟨h⟩ ↦ h) fun h ↦ ⟨h⟩

class IsEmpty (α : Sort _) : Prop where
  protected false : α → False

@[elab_as_elim]
def isEmptyElim [IsEmpty α] {p : α → Sort _} (a : α) : p a :=
  (IsEmpty.false a).elim

@[elab_as_elim]
protected def IsEmpty.elim {α : Sort u} (_ : IsEmpty α) {p : α → Sort _} (a : α) : p a :=
  (IsEmpty.false a).elim

@[simp]
theorem not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α :=
  ⟨fun h ↦ ⟨fun x ↦ h ⟨x⟩⟩, fun h1 h2 ↦ h2.elim h1.elim⟩

@[simp]
theorem isEmpty_Prop {p : Prop} : IsEmpty p ↔ ¬p := by
  simp only [← not_nonempty_iff, nonempty_Prop]

class Preorder (α : Type u) extends LE α where
  le_refl : ∀ a : α, a ≤ a

theorem le_refl [Preorder α] : ∀ a : α, a ≤ a :=
  Preorder.le_refl

theorem le_of_eq [Preorder α] {a b : α} : a = b → a ≤ b := fun h => h ▸ le_refl a

abbrev Eq.le := @le_of_eq

@[simp] theorem le_of_subsingleton [Preorder α] [Subsingleton α] {a b : α} : a ≤ b := (Subsingleton.elim a b).le

theorem iff_of_true' (ha : a) (hb : b) : a ↔ b := Iff.intro (fun _ => hb) (fun _ => ha)
theorem iff_true_intro' (h : a) : a ↔ True := iff_of_true' h trivial

@[simp]
theorem IsEmpty.forall_iff [IsEmpty α] {p : α → Prop} : (∀ a, p a) ↔ True :=
  iff_true_intro' isEmptyElim

@[simp] theorem and_imp' : (a ∧ b → c) ↔ (a → b → c) := ⟨fun h ha hb => h ⟨ha, hb⟩, fun h ⟨ha, hb⟩ => h ha hb⟩
@[simp] theorem not_and'' : ¬(a ∧ b) ↔ (a → ¬b) := and_imp'

set_option tactic.skipAssignedInstances false in
/--
error: simp made no progress
-/
#guard_msgs in
example [Preorder α] {a : α} {p : α → Prop} : ∀ (a_1 : α), a ≤ a_1 ∧ p a_1 → a ≤ a_1 := by
  simp only [isEmpty_Prop, not_and'',  forall_swap, le_of_subsingleton, IsEmpty.forall_iff] -- should not loop

theorem dec_and (p q : Prop) [Decidable (p ∧ q)] [Decidable p] [Decidable q] : decide (p ∧ q) = (p && q) := by
  by_cases p <;> by_cases q <;> simp [*]

theorem dec_not (p : Prop) [Decidable (¬p)] [Decidable p] : decide (¬p) = !p := by
  by_cases p <;> simp [*]

example [Decidable u] [Decidable v] : decide (u ∧ (v → False)) = (decide u && !decide v) := by
  simp only [imp_false]
  rw [dec_and]
  rw [dec_not]

set_option tactic.skipAssignedInstances false in
/--
error: tactic 'rewrite' failed, failed to assign synthesized instance
u v : Prop
inst✝¹ : Decidable u
inst✝ : Decidable v
⊢ decide (u ∧ ¬v) = (decide u && !decide v)
-/
#guard_msgs in
example [Decidable u] [Decidable v] : decide (u ∧ (v → False)) = (decide u && !decide v) := by
  simp only [imp_false]
  rw [dec_and]
  rw [dec_not]
