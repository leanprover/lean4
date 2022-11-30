def Set (α : Type u) := α → Prop
def Mem (a : α) (s : Set α) := s a
def image (f : α → β) (s : Set α) : Set β := fun b => ∃ a, Mem a s ∧ f a = b

@[congr] theorem image_congr {f g : α → β} {s : Set α} (h : ∀ a, Mem a s → f a = g a) : image f s = image g s :=
  sorry

example {Γ: Set Nat}: (image (Nat.succ ∘ Nat.succ) Γ) = (image (fun a => a.succ.succ) Γ) := by
  simp only [Function.comp_apply]
