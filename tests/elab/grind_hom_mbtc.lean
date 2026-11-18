example {C : Type} (h : Fin 4 → C) (x y z : Fin 4)
    : y + 1 ≤ x → x ≤ z → z ≤ y + 1 → h x = h (y + 1) := by
  grind

example {C : Type} (h : Fin 4 → C) (x : Fin 4)
    : 3 ≤ x → x ≤ 3 → h x = h (-1) := by
  grind

example {C : Type} (h : BitVec 2 → C) (x : BitVec 2)
    : 3 ≤ x → x ≤ 3 → h x = h (-1) := by
  grind

example {C : Type} (h : UInt8 → C) (x y z w : UInt8)
    : y + 1 + w ≤ x + w → x + w ≤ z → z ≤ y + w + 1 → h (x + w) = h (y + w + 1) := by
  grind

example {C : Type} (h : UInt16 → C) (x y z w : UInt16)
    : y + 1 + w ≤ x + w → x + w ≤ z → z ≤ y + w + 1 → h (x + w) = h (y + w + 1) := by
  grind

example {C : Type} (h : UInt32 → C) (x y z w : UInt32)
    : y + 1 + w ≤ x + w → x + w ≤ z → z ≤ y + w + 1 → h (x + w) = h (y + w + 1) := by
  grind

example {C : Type} (h : UInt64 → C) (x y z w : UInt64)
    : y + 1 + w ≤ x + w → x + w ≤ z → z ≤ y + w + 1 → h (x + w) = h (y + w + 1) := by
  grind

example {C : Type} (h : Nat → C) (x y z w r : Nat)
    : y + 1 + w ≤ x + w → x + w ≤ r → r ≤ x + w → x + w ≤ z → z ≤ y + w + 1 → h r = h (y + w + 1) := by
  grind

example {C : Type} (h : Fin 8 → C) (x y w r : Fin 8)
    : y + 1 + w ≤ r → r ≤ y + w + x → x = 1 → h r = h (y + w + 1) := by
  grind

example (f : Nat → Fin 2) : f a ≠ 0 → f a ≠ 1 → False := by
  grind
