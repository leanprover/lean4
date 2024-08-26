def Set (α : Type u) := α → Prop

def setOf {α : Type u} (p : α → Prop) : Set α :=
p

namespace Set

protected def mem (s : Set α) (a : α) :=
s a

instance : Membership α (Set α) :=
⟨Set.mem⟩

theorem ext {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b :=
funext (fun x => propext (h x))

protected def subset (s₁ s₂ : Set α) :=
∀ {a}, a ∈ s₁ → a ∈ s₂

class Subset (α : Type u) where
  /-- Subset relation: `a ⊆ b`  -/
  subset : α → α → Prop

/-- Subset relation: `a ⊆ b`  -/
infix:50 " ⊆ " => Subset.subset

instance : Subset (Set α) :=
⟨Set.subset⟩

instance : EmptyCollection (Set α) :=
⟨λ _ => False⟩

example (U : Type) (A B : Set U) : A ⊆ B → A = A :=
  fun h =>
  match @h with | (h : A ⊆ B) => sorry

example (U : Type) (A B : Set U) : A ⊆ B → A = A := by
  intro (h : A ⊆ B)
  sorry
