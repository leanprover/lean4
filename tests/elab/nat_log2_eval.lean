import Lean

/-!
Tests for literal evaluation of `Nat.log2` in `simp`/`seval`, in `sym => simp` (via
`Sym.Simp.evalGround`) and in `sym => dsimp` (via `Sym.DSimp.evalGround`).
-/

section
variable (x : Nat)

#check_simp x = Nat.log2 0 ~> x = 0
#check_simp x = Nat.log2 1 ~> x = 0
#check_simp x = Nat.log2 8 ~> x = 3
#check_simp x = Nat.log2 1000 ~> x = 9

end

example : Nat.log2 32 = 5 := by simp only [seval]

example : Nat.log2 (2 ^ 100) = 100 := by simp

register_sym_simp log2Ground where
  post := ground

example : Nat.log2 8 = 3 := by
  sym => simp log2Ground

example : Nat.log2 (2 ^ 100) = 100 := by
  sym => simp log2Ground

example (x : Nat) (h : x = 3) : x = Nat.log2 8 := by
  sym =>
    dsimp
    exact h
