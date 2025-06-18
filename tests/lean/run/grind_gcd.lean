open Nat

theorem gcd_self (n : Nat) : gcd n n = n := by grind

theorem gcd_eq_left_iff_dvd : gcd m n = m ↔ m ∣ n :=
  ⟨by grind, by grind [gcd_eq_iff]⟩

theorem gcd_eq_right_iff_dvd : gcd n m = m ↔ m ∣ n := by
  grind [Nat.gcd_eq_left_iff_dvd]

theorem lcm_self (m : Nat) : lcm m m = m := by grind

theorem lcm_lcm_self_right_left (m n : Nat) : lcm m (lcm m n) = lcm m n := by grind

theorem lcm_lcm_self_right_right (m n : Nat) : lcm m (lcm n m) = lcm m n := by grind

theorem neg_fmod_self (a : Int) : (-a).fmod a = 0 := by grind

theorem bmod_self {a : Nat} : Int.bmod a a = 0 := by grind

theorem neg_bmod_self {a : Nat} : Int.bmod (-a) a = 0 := by grind
