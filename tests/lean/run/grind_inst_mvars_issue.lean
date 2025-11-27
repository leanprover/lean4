namespace Nat

def ascFactorial (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => (n + k) * ascFactorial n k

def descFactorial (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => (n - k) * descFactorial n k

theorem descFactorial_of_lt {n : Nat} : ∀ {k : Nat}, n < k → n.descFactorial k = 0 := by sorry

theorem add_descFactorial_eq_ascFactorial' (n : Nat) :
    ∀ k : Nat, (n + k - 1).descFactorial k = n.ascFactorial k := by sorry

def ascFactorialBinary (n k : Nat) : Nat :=
  match k with
  | 0 => 1
  | 1 => n
  | k@(_ + 2) => ascFactorialBinary n (k / 2) * ascFactorialBinary (n + k / 2) ((k + 1) / 2)

theorem ascFactorial_eq_ascFactorialBinary : ascFactorial = ascFactorialBinary := sorry

def descFactorialBinary (n k : Nat) : Nat :=
  if n < k then 0
  else ascFactorialBinary (n - k + 1) k

theorem descFactorial_eq_descFactorialBinary : descFactorial = descFactorialBinary := by
  ext n k
  rw [descFactorialBinary]
  split <;> rename_i h
  · rw [descFactorial_of_lt h]
  · rw [← ascFactorial_eq_ascFactorialBinary, ← add_descFactorial_eq_ascFactorial']
    grind

end Nat
