/-!
# Delaborating structure instances
-/

structure A where
  x : Nat

structure B extends A where
  y : Nat

/-!
Check flattening of parent structures.
-/

/-- info: { x := 1 } : A -/
#guard_msgs in #check {x := 1 : A}

/-- info: { x := 1, y := 2 } : B -/
#guard_msgs in #check {x := 1, y := 2 : B}

/-!
No flattening of parent structures
-/
section
set_option pp.structureInstances.flatten false

/-- info: { x := 1 } : A -/
#guard_msgs in #check {x := 1 : A}

/-- info: { toA := { x := 1 }, y := 2 } : B -/
#guard_msgs in #check {x := 1, y := 2 : B}
end

/-!
Not a true parent structure, so no flattening.
-/

structure B' where
  toA : A
  y : Nat

/-- info: { toA := { x := 1 }, y := 2 } : B' -/
#guard_msgs in #check {toA := {x := 1}, y := 2 : B'}

/-!
Check that this handles parameters.
-/
structure C (n : Nat) where
  x : Fin n

structure D (n : Nat) extends C n where
  y : Nat

/-- info: { x := 1, y := 2 } : D 3 -/
#guard_msgs in #check {x := 1, y := 2 : D 3}
