module
variable {R : Type} [Lean.Grind.CommRing R]
-- My real code uses CommRing from Mathlib instead, and sees the same behavior.

def P : Nat → R → R → R
| 0, _, _ => 1
| n+1, x, y => (x + y - 1) * (y + 1) * P n x (y + 2) + (y - y^2) * P n x y

def S : Nat → R → R → R
| n, x, y => ((x + y)^2 - 1) * (y + 1) * (x + 1) * P n (y + 2) (x + 2)

theorem foo (n : Nat)
    (ih : ∀ m < n + 1 + 1, ∀ (x y : R), P m x y = P m y x)
    (h2 :
      ∀ (x y : R),
        (x + y - 1) * (y + 1) * P n.succ (y + 2) x =
        S n x y + (x + y - 1) * (y + 1) * (x - x ^ 2) * P n (y + 2) x)
    (m : Nat) (hm : m < n.succ.succ) (x y : R) :
    ((x + y) ^ 2 - 1) * (y + 1) * (x + 1) * P m (y + 2) (x + 2) =
      ((y + x) ^ 2 - 1) * (x + 1) * (y + 1) * P m (x + 2) (y + 2) := by
  grind
