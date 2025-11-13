section Mathlib.Order.Monotone.Defs

variable {α β : Type} [LT α] [LE α] [LE β] {f : α → β} {a b : α}

def Monotone (f : α → β) : Prop := ∀ ⦃a b⦄, a ≤ b → f a ≤ f b

theorem Monotone.imp (hf : Monotone f) (h : a ≤ b) : f a ≤ f b := sorry

theorem monotone_iff_forall_lt : Monotone f ↔ ∀ ⦃a b⦄, a < b → f a ≤ f b := sorry

end Mathlib.Order.Monotone.Defs

/--
error: `grind` failed
case grind.1.1.1.1.1.1.1.1.1
h : ¬Monotone fun n => n ^ n
w : Nat
h_2 : ¬∀ ⦃b : Nat⦄, w + 1 ≤ b → w ^ w ≤ b ^ b
w_1 : Nat
h_4 : ¬(w + 1 ≤ w_1 → w ^ w ≤ w_1 ^ w_1)
h_5 :
  ((w_1 ^ w_1) ^ w_1 ^ w_1) ^ (w_1 ^ w_1) ^ w_1 ^ w_1 =
    (((w + 1) ^ (w + 1)) ^ (w + 1) ^ (w + 1)) ^ ((w + 1) ^ (w + 1)) ^ (w + 1) ^ (w + 1)
h_6 :
  ((w ^ w) ^ w ^ w) ^ (w ^ w) ^ w ^ w =
    (((w_1 ^ w_1) ^ w_1 ^ w_1) ^ (w_1 ^ w_1) ^ w_1 ^ w_1) ^ ((w_1 ^ w_1) ^ w_1 ^ w_1) ^ (w_1 ^ w_1) ^ w_1 ^ w_1
h_7 : (w ^ w) ^ w ^ w = ((w_1 ^ w_1) ^ w_1 ^ w_1) ^ (w_1 ^ w_1) ^ w_1 ^ w_1
h_8 : (w ^ w) ^ w ^ w = ((w_1 + 1) ^ (w_1 + 1)) ^ (w_1 + 1) ^ (w_1 + 1)
h_9 : w ^ w = ((w + 1) ^ (w + 1)) ^ (w + 1) ^ (w + 1)
h_10 : (w_1 ^ w_1 + 1) ^ w_1 ^ w_1 * (w_1 ^ w_1 + 1) = ((w_1 ^ w_1) ^ w_1 ^ w_1) ^ (w_1 ^ w_1) ^ w_1 ^ w_1
h_11 :
  (w ^ w + 1) ^ w ^ w * (w ^ w + 1) =
    (((w_1 ^ w_1) ^ w_1 ^ w_1) ^ (w_1 ^ w_1) ^ w_1 ^ w_1) ^ ((w_1 ^ w_1) ^ w_1 ^ w_1) ^ (w_1 ^ w_1) ^ w_1 ^ w_1
h_12 : (w_1 ^ w_1) ^ w_1 ^ w_1 + 1 = (((w + 1) ^ (w + 1)) ^ (w + 1) ^ (w + 1)) ^ ((w + 1) ^ (w + 1)) ^ (w + 1) ^ (w + 1)
h_13 :
  (w ^ w) ^ w ^ w + 1 =
    (((w_1 ^ w_1) ^ w_1 ^ w_1) ^ (w_1 ^ w_1) ^ w_1 ^ w_1) ^ ((w_1 ^ w_1) ^ w_1 ^ w_1) ^ (w_1 ^ w_1) ^ w_1 ^ w_1
⊢ False
-/
#guard_msgs in
theorem pow_self_mono : Monotone fun n : Nat ↦ n ^ n := by
  grind -verbose [
    monotone_iff_forall_lt,
    Monotone.imp,
    Nat.lt_pow_self
  ]
