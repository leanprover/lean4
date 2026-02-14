-- Issue #12245: grind works on Fin n but fails on Fin (n + 1)
-- The fix is in `getPatternArgKinds`: `outParam` arguments are now treated as support
-- in e-matching patterns. After the next toolchain update, the `attribute` line below
-- can be removed.
attribute [grind =] Fin.val_zero Fin.val_one Fin.le_def Fin.lt_def

example {n : Nat} {a : Fin n} {b : Nat} (hb : b < n)
    (h : (a : Nat) < b) : a < ⟨b, hb⟩ := by grind

example {n : Nat} {a : Fin (n + 1)} {b : Nat} (hb : b < n + 1)
    (h : (a : Nat) < b) : a < ⟨b, hb⟩ := by grind

example {n : Nat} {a : Fin (n + 2)} {b : Nat} (hb : b < n + 2)
    (h : (a : Nat) < b) : a < ⟨b, hb⟩ := by grind

example {n m : Nat} {a : Fin (n + m)} {b : Nat} (hb : b < n + m)
    (h : (a : Nat) < b) : a < ⟨b, hb⟩ := by grind

example {n : Nat} {a : Fin (n * 2 + 1)} {b : Nat} (hb : b < n * 2 + 1)
    (h : (a : Nat) < b) : a < ⟨b, hb⟩ := by grind
