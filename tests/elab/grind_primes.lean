-- This is the example from the front page of the website
-- There's no mechanism keeping it in sync with the website,
-- but nevertheless it's better than nothing.

/-- A prime is a number larger than 1 with no trivial divisors -/
def IsPrime (n : Nat) := 1 < n ∧ ∀ k, 1 < k → k < n → ¬ k ∣ n

/-- Every number larger than 1 has a prime factor -/
theorem exists_prime_factor :
    ∀ n, 1 < n → ∃ k, IsPrime k ∧ k ∣ n := by
  intro n h1
  -- Either `n` is prime...
  by_cases hprime : IsPrime n
  · grind [Nat.dvd_refl]
  -- ... or it has a non-trivial divisor with a prime factor
  · obtain ⟨k, _⟩ : ∃ k, 1 < k ∧ k < n ∧ k ∣ n := by
      simp_all [IsPrime]
    obtain ⟨p, _, _⟩ := exists_prime_factor k (by grind)
    grind [Nat.dvd_trans]

/-- The factorial, defined recursively, with custom notation -/
def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n + 1) * factorial n
notation:10000 n "!" => factorial n

/-- The factorial is always positive -/
theorem factorial_pos : ∀ n, 0 < n ! := by
  intro n; induction n <;>
    grind [factorial, Nat.mul_pos_iff_of_pos_left]

/-- ... and divided by its constituent factors -/
theorem dvd_factorial : ∀ n, ∀ k ≤ n, 0 < k → k ∣ n ! := by
  intro n; induction n <;>
    grind [Nat.dvd_mul_right, Nat.dvd_mul_left_of_dvd, factorial]

/--
We show that we find arbitrary large (and thus infinitely
many) prime numbers, by picking an arbitrary number `n`
and showing that `n! + 1` has a prime factor larger than `n`.
-/
theorem InfinitudeOfPrimes : ∀ n, ∃ p > n, IsPrime p := by
  intro n
  have : 1 < n ! + 1 := by grind [factorial_pos]
  obtain ⟨p, hp, _⟩ := exists_prime_factor (n ! + 1) this
  suffices ¬p ≤ n by grind
  intro (_ : p ≤ n)
  have : 1 < p := hp.1
  have : p ∣ n ! := dvd_factorial n p ‹p ≤ n› (by grind)
  have := Nat.dvd_sub ‹p ∣ n ! + 1› ‹p ∣ n !›
  grind [Nat.add_sub_cancel_left, Nat.dvd_one]
