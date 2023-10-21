@[inline] def decidable_of_iff {b : Prop} (a : Prop) (h : a ↔ b) [Decidable a] : Decidable b :=
  decidable_of_decidable_of_iff h

theorem LE.le.lt_or_eq_dec {a b : Nat} (hab : a ≤ b) : a < b ∨ a = b :=
by cases hab
   · exact .inr rfl
   · refine .inl ?_ ; refine Nat.succ_le_succ ?_ ; assumption

section succeeds_using_match

local instance decidableBallLT :
  ∀ (n : Nat) (P : ∀ k, k < n → Prop) [∀ n h, Decidable (P n h)], Decidable (∀ n h, P n h)
| 0, _, _ => isTrue fun _ => (by cases ·)
| (n+1), P, H =>
  match decidableBallLT n (P · <| Nat.le_succ_of_le ·) with
  | isFalse h => isFalse (h fun _ _ => · _ _)
  | isTrue h =>
    match H n Nat.le.refl with
    | isFalse p => isFalse (p <| · _ _)
    | isTrue p => isTrue fun _ h' => (Nat.le_of_lt_succ h').lt_or_eq_dec.elim (h _) (· ▸ p)

set_option maxHeartbeats 5000
example : ∀ a, a < 9 → ∀ b, b < 9 → ∀ c, c < 9 → a ^ 2 + b ^ 2 + c ^ 2 ≠ 7 := by decide

end succeeds_using_match

section fails_with_timeout

-- we change `match decidableBallLT` to `by cases decidableBallLT' ... exact`:
local instance decidableBallLT' :
  ∀ (n : Nat) (P : ∀ k, k < n → Prop) [∀ n h, Decidable (P n h)], Decidable (∀ n h, P n h)
| 0, _, _ => isTrue fun _ => (by cases ·)
| (n+1), P, H => by
  cases decidableBallLT' n (P · <| Nat.le_succ_of_le ·) with
  | isFalse h => exact isFalse (h fun _ _ => · _ _)
  | isTrue h =>
    exact match H n Nat.le.refl with
    | isFalse p => isFalse (p <| · _ _)
    | isTrue p => isTrue fun _ h' => (Nat.le_of_lt_succ h').lt_or_eq_dec.elim (h _) (· ▸ p)

set_option maxHeartbeats 5000
example : ∀ a, a < 9 → ∀ b, b < 9 → ∀ c, c < 9 → a ^ 2 + b ^ 2 + c ^ 2 ≠ 7 := by decide

end fails_with_timeout
