open BitVec

variable (write : (n : Nat) → BitVec 64 → BitVec (n * 8) → Type → Type)

theorem write_simplify_test_0 (a x y : BitVec 64)
  (h : ((8 * 8) + 8 * 8) = 2 * ((8 * 8) / 8) * 8) :
  write (2 * ((8 * 8) / 8)) a (BitVec.cast h (zeroExtend (8 * 8) x ++ (zeroExtend (8 * 8) y))) s
  =
  write 16 a (x ++ y) s := by
  simp only [setWidth_eq, BitVec.cast_eq]

/--
info: write : (n : Nat) → BitVec 64 → BitVec (n * 8) → Type → Type
s aux : Type
a x y : BitVec 64
h : 128 = 128
⊢ write 16 a (x ++ y) s = aux
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (a x y : BitVec 64)
  (h : ((8 * 8) + 8 * 8) = 2 * ((8 * 8) / 8) * 8) :
  write (2 * ((8 * 8) / 8)) a (BitVec.cast h (zeroExtend (8 * 8) x ++ (zeroExtend (8 * 8) y))) s
  =
  aux := by
  simp
  dsimp at h
  trace_state
  sorry
