open Fin

example (a b : Fin n) : (a % b).val = a.val % b.val := by grind

example (a b : Fin n) : (a * b).val = (a.val * b.val) % n := by grind

example (a : Fin n) : a < n := by grind

example {a b : Fin n} : a.1 ≠ b.1 ↔ a ≠ b := by grind

example (a : Fin n) : a < n := by grind

example {a b : Fin n} : a.1 ≠ b.1 ↔ a ≠ b := by grind

example (a : Fin 1) : a.val = 0 := by grind
example (a : Fin 2) : a.val = 0 ∨ a.val = 1 := by grind

example (a : Fin 37) : a.val < 47 := by grind
example (a : Fin (n + 37)) : a.val < n + 47 := by grind
example (a : Fin (2 * n + 1)) : a.val < 2 * (n + 1) := by grind

example {a b : Fin n} : a ≤ b ↔ a.1 ≤ b.1 := by grind
example {a b : Fin n} : a < b ↔ a.1 < b.1 := by grind
example {a b : Fin n} : a < b ↔ a.val < b.val := by grind
example {a b : Fin n} : ¬ a ≤ b ↔ b < a := by grind
example {a b : Fin n} : ¬ a < b ↔ b ≤ a := by grind
example (a : Fin n) : a ≤ a := by grind
example (a : Fin n) : ¬ a < a := by grind
example {a b c : Fin n} : a ≤ b → b ≤ c → a ≤ c := by grind
example {a b c : Fin n} : a < b → b < c → a < c := by grind
example (a b : Fin n) : a ≤ b ∨ b ≤ a := by grind
example {a b : Fin n} (h : a < b) : ¬ b < a := by grind
example {a b : Fin n} (h : a < b) : a ≠ b := by grind
example {a b : Fin n} (h : a < b) : b ≠ a := by grind
example {a b : Fin n} (h : a < b) : a ≤ b := by grind
example {a b c : Fin n} : a ≤ b → b < c → a < c := by grind
example {a b c : Fin n} : a < b → b ≤ c → a < c := by grind
example {a : Fin n} : a ≤ a := by grind
example {a b : Fin n} : a < b ↔ a ≤ b ∧ a ≠ b := by grind
example {a b : Fin n} (h : a ≠ b) : a < b ∨ b < a := by grind
example (a b : Fin n) : a < b ∨ b ≤ a := by grind
example (a b : Fin n) : a ≤ b ∨ b < a := by grind
example {a b : Fin n} (hab : a = b) : a ≤ b := by grind
example {a b : Fin n} (hab : a = b) : b ≤ a := by grind
example {a b : Fin n} : a ≤ b → a = b ∨ a < b := by grind
example {a b : Fin n} : a ≤ b → a < b ∨ a = b := by grind
example (i : Fin (n + 1)) : i.1 ≤ n := by grind

example {x y : Fin n} : x = y ↔ x ≤ y ∧ y ≤ x := by grind

example : (Fin.last 0 : Fin 1) = 0 := by grind

example (h : n ≤ m) (i : Fin n) : (castLE h i : Nat) = i := by grind

example {k : Nat} (h : n = m) (h' : m = k) {i : Fin n} :
    (i.cast h).cast h' = i.cast (Eq.trans h h') := by grind

example (n : Nat) (j : Fin n) :
    j.succ.castSucc = (j.castSucc).succ := by grind

example {n : Nat} (i : Fin n) : i.castSucc.succ = i.succ.castSucc := by grind

example {m n : Nat} {i : Fin m} : natAdd n (castSucc i) = castSucc (natAdd n i) := by grind

example (i : Fin n) : i.succ.castSucc = i.castSucc.succ := by grind

example (h : n ≤ n) (i : Fin n) : i.castLE h = i := by grind

example (h : n ≤ m) (i : Fin n) :
    (i.castLE h).castSucc = i.castLE (by omega) := by grind

example (n : Nat) (i : Fin k) :
    (i.natAdd n).castSucc = (i.castSucc).natAdd n := by grind

example : ∀ {a b : Fin 2}, (a = 0 ↔ b = 0) → a = b := by grind

example [NeZero n] {x : Fin n} : x - x = 0 := by grind

example {n : Nat} : ∀ a b : Fin n, (a * b).val = a.val * b.val % n := by grind

example {n : Nat} : ∀ a b : Fin n, ((a * b : Fin n) : Nat) = a * b % n := by grind

example [i : NeZero n] (k : Fin n) : k * 1 = k := by grind

example (a b : Fin n) : a * b = b * a := by grind

example (a b c : Fin n) : a * b * c = a * (b * c) := by grind

example [NeZero n] (k : Fin n) : (1 : Fin n) * k = k := by grind

example [NeZero n] (k : Fin n) : k * 0 = 0 := by grind

example [NeZero n] (k : Fin n) : (0 : Fin n) * k = 0 := by grind
