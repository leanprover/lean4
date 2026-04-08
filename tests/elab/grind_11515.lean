example {x m n : Nat} (h : x = 4 ^ (m + 1) * n) : x % 4 = 0 := by
  grind

/--
info: Try these:
  [apply] grind only [usr Nat.div_pow_of_pos, usr Nat.dvd_mul_right_of_dvd]
  [apply] grind =>
    instantiate only [usr Nat.div_pow_of_pos]
    instantiate only [usr Nat.dvd_mul_right_of_dvd]
    lia
-/
#guard_msgs in
example {x m n : Nat} (h : x = 4 ^ (m + 1) * n) : x % 4 = 0 := by
  grind?

example {x m n : Nat} (h : x = 4 ^ (m + 1) * n) : x % 4 = 0 := by
  grind only [usr Nat.div_pow_of_pos, usr Nat.dvd_mul_right_of_dvd]

example {x m n : Nat} (h : x = 4 ^ (m + 1) * n) : x % 4 = 0 := by
  grind =>
    instantiate only [usr Nat.div_pow_of_pos]
    instantiate only [usr Nat.dvd_mul_right_of_dvd]
    lia

example {x m n : Nat} (h₁ : x = 4 ^ (m + 1) * n) : x % 4 = 0 := by
  grind

example {x m n : Nat} (h₁ : x = 4 ^ m * n) : m > 0 → x % 4 = 0 := by
  grind

example {x m n : Nat} (h₁ : x = n * 4 ^ (m + 1) * n) : x % 4 = 0 := by
  grind

example {a b x m n : Nat} (h₁ : x = b * a * 4 ^ (m + 1) * n) : x % 4 = 0 := by
  grind

example {a b x m n : Nat} (h₁ : x = b * 4 ^ m * a * 3 ^ n) : n > 0 → m > 0 → x % 12 = 0 := by
  grind

example {a b x m n : Nat} (h₁ : x = b * 4 ^ m * a * 3 ^ n) : n > 0 → m > 0 → x % 6 = 0 := by
  grind

example (m n : Nat) (h : 4 ∣ m) : 4 ∣ m * n := by
  grind

example (a m n : Nat) (h : a ∣ m) : a ∣ m * n := by
  grind

example (a m n o p : Nat) : a ∣ m → a ∣ m * n * o * p := by
  grind

example {a b x m n : Nat}
    : x = b * 4 ^ m * a → a = 3^n → n > 0 → m > 0 → x % 12 = 0 := by
  grind

example {a b x m n : Nat}
    : n > 0 → x = b * 4^m * a → a = 9^n → m > 0 → x % 6 = 0 := by
  grind

example {a n : Nat}
    : a = 2^(3^n) → a % 2 = 0 := by
  grind

example {a n : Nat}
    : m > 4 → a = 2^(m^n) → a % 2 = 0 := by
  grind
