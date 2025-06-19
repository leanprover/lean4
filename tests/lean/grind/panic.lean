open List

theorem set_append {s t : List α} :
    (s ++ t).set i x = if i < s.length then s.set i x ++ t else s ++ t.set (i - s.length) x := by
  induction s generalizing i with
  | nil => grind only [= append_assoc, Int.dvd_mul_right, length_nil, Nat.dvd_mul_right, nil_append,
    = Nat.zero_dvd, append_nil, Nat.dvd_refl, Int.dvd_mul_left, length_append, Nat.dvd_zero, =_
    append_assoc, → eq_nil_of_append_eq_nil, Nat.dvd_mul_left, cases Or]
  | cons a as ih => cases i with grind (splits := 12) [-List.set_append]
