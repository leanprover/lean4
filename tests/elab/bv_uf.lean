import Std.Tactic.BVDecide

example (f : BitVec 8 → BitVec 8) (x y : BitVec 8) (h : x = y) :
    f x = f y := by
  bv_decide +uf

example (f g : BitVec 8 → BitVec 8) (x y : BitVec 8) (h : x = y) :
    f (g x) = f (g y) := by
  bv_decide +uf

example (f g : {w : Nat} → BitVec w → BitVec w) (x y : BitVec 8) (h : x = y) :
    f (g x) = f (g y) := by
  bv_decide +uf

example (f g : {w : Nat} → BitVec w → BitVec w) (x y : BitVec 8) (h : x = y)
    (x' y' : BitVec 16) (h' : x' = y') :
    f (g x) = f (g y) ∧ f (g x') = f (g y') := by
  bv_decide +uf

example (f : BitVec 8 → BitVec 16 → BitVec 8) (x y : BitVec 8) (x' y' : BitVec 16) (h1 : x = y)
    (h2 : x' = y') : f x x' = f y y' := by
  bv_decide +uf

example (f : BitVec 8 → Bool → BitVec 8) (x y : BitVec 8) (x' y' : Bool) (h1 : x = y)
    (h2 : x' = y') : f x x' = f y y' := by
  bv_decide +uf

example (f g : {w : Nat} → BitVec w → BitVec 16 → BitVec w) (x y : BitVec 8) (x' y' : BitVec 16)
    (h : x = y) (h2 : x' = y') : f (g x x') y' = f (g y y') y' := by
  bv_decide +uf

example (xs : List (BitVec 8)) (h : xs.foldl (fun acc x => acc + x) 0 = 5) :
    xs.foldl (fun acc x => acc + x) 0 ≠ 6 := by
  bv_decide

example (f : BitVec 8 → BitVec 8) (c : Bool) (x y z : BitVec 8) (hx : x = 0) (hy : x = y) (hz : z = 0) :
    f (bif c then x else y) = f z := by
  bv_decide +uf

example (f : BitVec 8 → Bool) (x y : BitVec 8) (h : x = y) :
    f x = f y := by
  bv_decide +uf

example (f : BitVec 8 → Bool → Bool) (x y : BitVec 8) (h : x = y) (x' y' : Bool) (h : x' = y') :
    f x x' = f y y' := by
  bv_decide +uf

example (f : Bool → BitVec 8) (g : Bool → Bool) (x : BitVec 8) (c : Bool)
    (h : x.getLsbD 3 = c) : f (x.getLsbD 3) = f c ∧ g (x.getLsbD 3) = g c := by
  bv_decide +uf

example (f : BitVec 8 → BitVec 8) (y : BitVec 8) : ∀ x : BitVec 8, x = y → f x = f y := by
  bv_decide +uf

/--
error: - The prover used the following expressions as uninterpreted functions:
  - f x
  - f y
The prover found a counterexample, consider the following assignment:
f x = 127#8
x = 255#8
f y = 255#8
y = 127#8
-/
#guard_msgs in
example (f : BitVec 8 → BitVec 8) (x y : BitVec 8) :
    f x = f y := by
  bv_decide +uf

/--
error: - The prover used the following expressions as uninterpreted functions:
  - f x
  - f y
The prover found a counterexample, consider the following assignment:
f x = false
x = 255#8
f y = true
y = 127#8
-/
#guard_msgs in
example (f : BitVec 8 → Bool) (x y : BitVec 8) :
    f x = f y := by
  bv_decide +uf

/--
error: bv_decide reached its round limit, consider increasing it via the `cegarRounds` config option
-/
#guard_msgs in
example (f : BitVec 8 → BitVec 8) (x y : BitVec 8) :
    f x = f y := by
  bv_decide (config := { uf := true, cegarRounds := 0 })
