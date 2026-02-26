/-!
# Delaborating structure instances
-/

structure A where
  x : Nat

/-!
Basic example
-/
/-- info: { x := 1 } : A -/
#guard_msgs in #check { x := 1 : A }

/-!
pp.all
-/
set_option pp.all true in
/-- info: A.mk (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) : A -/
#guard_msgs in #check { x := 1 : A }

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

/-!
Show type
-/
set_option pp.structureInstanceTypes true in
/-- info: { x := 0 : A } : A -/
#guard_msgs in #check { x := 0 : A }

/-!
Omit default values
-/

/-- info: { } : Lean.Meta.Simp.Config -/
#guard_msgs in #check { : Lean.Meta.Simp.Config }

structure E where
  n : Nat := 0

/-- info: { } : E -/
#guard_msgs in #check { : E }

/-- info: { n := 1 } : E -/
#guard_msgs in #check { n := 1 : E }

set_option pp.structureInstances.defaults true in
/-- info: { n := 0 } : E -/
#guard_msgs in #check { : E }

structure F extends E where
  m : Nat := 1

/-- info: { } : F -/
#guard_msgs in #check { : F }
set_option pp.structureInstances.defaults true in
/-- info: { n := 0, m := 1 } : F -/
#guard_msgs in #check { : F }
/-- info: { n := 1 } : F -/
#guard_msgs in #check { n := 1 : F }
/-- info: { m := 2 } : F -/
#guard_msgs in #check { m := 2 : F }

/-!
Omit default values, with parameter handling
-/

structure G (n : Nat) where
  m := n

/-- info: { } : G 3 -/
#guard_msgs in #check { : G 3 }
/-- info: { m := 2 } : G 3 -/
#guard_msgs in #check { m := 2 : G 3 }


/-!
Explicit mode turns off structure instance notation iff there are parameters
-/

set_option pp.explicit true in
/-- info: { } : E -/
#guard_msgs in #check { : E }

set_option pp.explicit true in
/--
info: @G.mk (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
  (@OfNat.ofNat Nat (nat_lit 3)
    (instOfNatNat (nat_lit 3))) : G (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
-/
#guard_msgs in #check { : G 3 }

/-!
If universe levels need to be shown, structure instance notation is turned off
-/

structure U (α : Type _) where
  x : α

/-- info: { x := 1 } : U Nat -/
#guard_msgs in #check { x := 1 : U Nat }

set_option pp.universes true in
/-- info: U.mk.{0} 1 : U.{0} Nat -/
#guard_msgs in #check { x := 1 : U Nat }

/-!
Dependence of default value
-/
structure H where
  x : Nat
  y : Nat := x

/-- info: { x := 1 } : H -/
#guard_msgs in #check { x := 1 : H }

/-!
Diamond inheritance
-/
structure D1 where
  x := 1
structure D2 extends D1 where
structure D3 extends D1 where
  x := 3
structure D4 extends D2, D3

/-- info: { } : D1 -/
#guard_msgs in #check { : D1 }
set_option pp.structureInstances.defaults true in
/-- info: { x := 1 } : D1 -/
#guard_msgs in #check { : D1 }

/-- info: { } : D2 -/
#guard_msgs in #check { : D2 }
set_option pp.structureInstances.defaults true in
/-- info: { x := 1 } : D2 -/
#guard_msgs in #check { : D2 }

/-- info: { } : D3 -/
#guard_msgs in #check { : D3 }
set_option pp.structureInstances.defaults true in
/-- info: { x := 3 } : D3 -/
#guard_msgs in #check { : D3 }

/-- info: { } : D4 -/
#guard_msgs in #check { : D4 }
set_option pp.structureInstances.defaults true in
/-- info: { x := 3 } : D4 -/
#guard_msgs in #check { : D4 }

/-!
Inheritance with parameters
-/
namespace Test1

structure A (α : Type) [Inhabited α] where
  x : α := default
structure B (β : Type) [Inhabited β] extends A β where

/-- info: { } : B Nat -/
#guard_msgs in #check { : B Nat }
set_option pp.structureInstances.defaults true in
/-- info: { x := default } : B Nat -/
#guard_msgs in #check { : B Nat }

-- Only reducible defeq, so the `x` fields is still included:
/-- info: { x := 0 } : B Nat -/
#guard_msgs in #check { x := 0 : B Nat }

end Test1
