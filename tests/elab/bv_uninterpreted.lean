import Std.Tactic.BVDecide

-- Demonstrate some arbitrary width reasoning
example {x y z : BitVec w} :
    (x &&& y) ||| (x &&& z) ||| (y &&& z) ||| x ||| y ||| z
      =
    ~~~ ((~~~ x) &&& (~~~ y) &&& (~~~ z)) := by
  ext i h
  simp [h]
  bv_decide

@[irreducible]
def ufBv (x : BitVec w) : BitVec w := x

example (x y : BitVec 16) : (ufBv x) + (ufBv y) = (ufBv y) + (ufBv x) := by bv_decide

@[irreducible]
def ufBool (x : Bool) : Bool := x

example (x y : BitVec 16) (z : Bool) : ((ufBool (x < y)) ∧ z) ↔ (z ∧ ufBool (x < y)) := by bv_decide

example (x y z : BitVec 16) (h1 : x < z) (h2 : z < (ufBv y)) : x < (ufBv y) := by bv_decide
