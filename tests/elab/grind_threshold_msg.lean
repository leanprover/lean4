/-!
Tests that the `grind` failure message reported without `+verbose` lists the thresholds that were
reached, as configuration items the user can raise.
-/

/--
error: `lia` has failed after reaching the threshold `(splits := 1)`, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x y z : Int) (c1 c2 c3 : Bool) :
    (if c1 then x else 0) + (if c2 then y else 0) + (if c3 then z else 0) ≤ x + y + z := by
  lia (splits := 1)

/--
error: `lia` has failed after reaching the threshold `(liaSteps := 1)`, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x y : Int) (h1 : 2*x + 3*y = 7) (h2 : 5 ≤ x) (h3 : x ≤ 100) (h4 : y ≥ 0) : False := by
  lia (liaSteps := 1)

/--
error: `grind` has failed after reaching the threshold `(ringSteps := 1)`, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example [Lean.Grind.CommRing α] (a b c : α) (h1 : a*b = c) (h2 : b*c = a) (h3 : c*a = b) : a = 1 := by
  grind (ringSteps := 1)

opaque f : Nat → Nat
axiom fax (x : Nat) : f x = f (f x) + 0
#guard_msgs (drop info) in
attribute [grind] fax

/--
error: `grind` has failed after reaching the threshold `(ematch := 2)`, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (a : Nat) : f a = 1 := by
  grind (ematch := 2)

/--
error: `grind` has failed after reaching the threshold `(gen := 2)`, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (a : Nat) : f a = 1 := by
  grind (gen := 2)

opaque g : Nat → Nat → Nat
axiom gax (x y : Nat) : g x y = g y x
#guard_msgs (drop info) in
attribute [grind] gax

/--
error: `grind` has failed after reaching the threshold `(instances := 3)`, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (a b c d : Nat) (h : g a b + g b c + g c d + g d a = 1) : False := by
  grind (instances := 3)

/--
error: `grind` has failed after reaching the thresholds `(instances := 3)` and `(gen := 1)`, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (a b c d : Nat) (h : g a b + g b c + g c d + g d a = 1) : False := by
  grind (instances := 3) (gen := 1)

/--
error: `grind` has failed after reaching the thresholds `(instances := 3)`, `(ematch := 1)`, and `(gen := 1)`, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (a b c d : Nat) (h : g a b + g b c + g c d + g d a = 1) : False := by
  grind (instances := 3) (ematch := 1) (gen := 1)

-- No threshold reached.
/--
error: `lia` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example (x : Int) (h : 0 ≤ x) : x > 5 := by
  lia
