section Mathlib.Order.Monotone.Defs

variable {α β : Type} [LT α] [LE α] [LE β] {f : α → β} {a b : α}

def Monotone (f : α → β) : Prop := ∀ ⦃a b⦄, a ≤ b → f a ≤ f b

theorem Monotone.imp (hf : Monotone f) (h : a ≤ b) : f a ≤ f b := sorry

theorem monotone_iff_forall_lt : Monotone f ↔ ∀ ⦃a b⦄, a < b → f a ≤ f b := sorry

end Mathlib.Order.Monotone.Defs

#guard_msgs (drop error) in
theorem pow_self_mono : Monotone fun n : Nat ↦ n ^ n := by
  grind -verbose [
    monotone_iff_forall_lt,
    Monotone.imp,
    Nat.lt_pow_self
  ]
