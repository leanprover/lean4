module
import Std.Tactic.BVDecide

/-!
Tests for propositional atoms in bv_decide
-/

example (q : Prop) (h1 : q) (h2 : ¬q) : False := by
  bv_decide

example (q : Prop) (x : BitVec 2) (h1 : x = 1 → q) (h2 : x = 1) (h3 : ¬q) : False := by
  bv_decide

example (q r : Prop) (h1 : q ↔ r) (h2 : q ∨ r) : q ∧ r := by
  bv_decide

example (q r : Prop) (h1 : q = r) (h2 : q) : r := by
  bv_decide

example (q : Prop) (b : Bool) (h1 : b = true ↔ q) (h2 : b) : q := by
  bv_decide

example (q : Prop) (x : BitVec 4) (h1 : x < 3 → q) (h2 : x = 2) : q := by
  bv_decide

example (q : Prop) [Decidable q] (x : BitVec 4) (h : q) : (if q then x else 0) = x := by
  bv_decide

example (q : Prop) [Decidable q] (h : q) : decide q = true := by
  bv_decide

/--
error: The prover found a counterexample, consider the following assignment:
x = 0#2
q = False
r = True
-/
#guard_msgs in
example (q r : Prop) (x : BitVec 2) (h1 : x = 1 → q) (h2 : r ∨ q) : False := by
  bv_decide
