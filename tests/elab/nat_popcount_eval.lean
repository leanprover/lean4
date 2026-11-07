module
import Lean
public meta import Lean
/-! Literal population counts in the simplifier and the symbolic evaluator. -/

example : Nat.popcount 255 = 8 := by simp
example : Nat.popcount (2^256-1) = 256 := by simp only [seval]

register_sym_simp popcountGround where
  post := ground

example : Nat.popcount 255 = 8 := by
  sym => simp popcountGround

example (x : Nat) (h : x = 8) : x = Nat.popcount 255 := by
  sym =>
    dsimp
    exact h
