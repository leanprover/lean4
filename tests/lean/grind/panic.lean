open List

-- PANIC
-- `Nat.dvd_mul_left` and `Nat.zero_dvd` are bad lemmas for `grind`, but we probably still shouldn't panic.
theorem set_append {s t : List α} :
    (s ++ t).set i x = if i < s.length then s.set i x ++ t else s ++ t.set (i - s.length) x := by
  induction s generalizing i with
  | nil => grind only [length_nil, nil_append, Nat.zero_dvd, length_append, =_ append_assoc, Nat.dvd_mul_left]
  | cons a as ih => sorry
