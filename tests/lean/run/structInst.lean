/-!
# Tests for structure instance notation
-/

-- Make sure defaults pretty print so we can see what they elaborate to.
set_option pp.structureInstances.defaults true

namespace Ex1

structure A where
(x : Nat)

structure B extends A where
(y : Nat := x + 2) (x := y + 1)

structure C extends B where
(z : Nat) (x := z + 10)

/-- info: { x := 1 + 1, y := 1 } : B -/
#guard_msgs in #check { y := 1 : B }
/-- info: { x := 1 + 10, y := 1 + 10 + 2, z := 1 } : C -/
#guard_msgs in #check { z := 1 : C }
/-! Make sure `z` is parsed as an abbreviation: -/
/-- info: fun z => { x := z + 10, y := z + 10 + 2, z := z } : Nat → C -/
#guard_msgs in #check fun z : Nat => { z : C }

def test1 : B where
  y := 1
def test2 : C where
  z := 1

end Ex1

namespace Ex2

structure A where
(x : Nat) (y : Nat)

structure B extends A where
(z : Nat := x + 1) (y := z + x)

/-- info: { x := 1, y := 1 + 1 + 1, z := 1 + 1 } : B -/
#guard_msgs in #check { x := 1 : B }

def test1 : B where
  x := 1

end Ex2

namespace Ex3

structure A where
(x : Nat)

structure B extends A where
(y : Nat := x + 2) (x := y + 1)

structure C extends B where
(z : Nat := 2*y) (x := z + 2) (y := z + 3)

-- This first example does not work because the default values at `C` are the only ones considered.
/--
error: fields missing: 'y', 'z'
---
info: { x := 1, y := sorry, z := sorry } : C
-/
#guard_msgs in #check { x := 1 : C }
/-- info: { x := 2 * 1 + 2, y := 1, z := 2 * 1 } : C -/
#guard_msgs in #check { y := 1 : C }
/-- info: { x := 1 + 2, y := 1 + 3, z := 1 } : C -/
#guard_msgs in #check { z := 1 : C }

-- This first example does not work because the default values at `C` are the only ones considered.
/-- error: fields missing: 'y', 'z' -/
#guard_msgs in
def test1 : C where
  x := 1
def test2 : C where
  y := 1
def test3 : C where
  z := 1

end Ex3

namespace Ex4

structure A where
(x : Nat)

structure B extends A where
(y : Nat := x + 1) (x := y + 1)

structure C extends B where
(z : Nat := 2*y) (x := z + 3)

/-- info: { x := 1, y := 1 + 1, z := 2 * (1 + 1) } : C -/
#guard_msgs in #check { x := 1 : C }
/-- info: { x := 2 * 1 + 3, y := 1, z := 2 * 1 } : C -/
#guard_msgs in #check { y := 1 : C }
/-- info: { x := 1 + 3, y := 1 + 3 + 1, z := 1 } : C -/
#guard_msgs in #check { z := 1 : C }
/-- info: { x := 2, y := 2 + 1, z := 1 } : C -/
#guard_msgs in #check { z := 1, x := 2 : C }
/-- info: { x := 1 + 1, y := 1 } : B -/
#guard_msgs in #check { y := 1 : B }

def test1 : C where
  x := 1
def test2 : C where
  y := 1
def test3 : C where
  z := 1
def test4 : C where
  z := 1
  x := 2
def test5 : C where
  y := 1

end Ex4

/-!
Binders example
-/
structure PosFun where
  f : Nat → Nat
  pos : ∀ n, 0 < f n

def p : PosFun :=
  { f n := n + 1
    pos := by simp }

def p_where : PosFun where
  f n := n + 1
  pos := by simp

/-!
Equations
-/
def p' : PosFun :=
  { f
      | 0 => 1
      | n + 1 => n + 1
    pos := by rintro (_|_) <;> simp }

def p'_where : PosFun where
  f
    | 0 => 1
    | n + 1 => n + 1
  pos := by rintro (_|_) <;> simp

/-!
Binders and type ascriptions
-/
namespace Ex5

structure A (α : Type) (β : Type) where
  x : α
  f : β → β
  z : α

/-- info: fun z => { x := 1, f := fun n => n + 1, z := z } : Int → A Int Int -/
#guard_msgs in #check fun z => { x : Int := 1, f n : Int := n + 1, z : A _ _ }

def test1 (z : Int) : A Int Int where
  x : Int := 1
  f n : Int := n + 1
  z

end Ex5

/-!
Default instances are applied before analyzing default values.
Without this, `α` would be reported as being a missing field.
-/
namespace Ex6
structure MyStruct where
    {α : Type u}
    {β : Type v}
    a : α
    b : β

/-- info: { α := Nat, β := Bool, a := 10, b := true } : MyStruct -/
#guard_msgs in #check { a := 10, b := true : MyStruct }
end Ex6

/-!
Make sure we have the Lean 3 behavior, where field projections are unfolded.
https://github.com/leanprover-community/mathlib4/issues/12129#issuecomment-2056134533
-/
namespace Mathlib12129

structure Foo where
  toFun : Nat → Nat

structure Bar extends Foo where
  prop : toFun 0 = 0

/-- info: ⊢ (fun x => x) 0 = 0 -/
#guard_msgs in
def bar : Bar where
  toFun x := x
  prop := by
    trace_state
    rfl

end Mathlib12129

/-!
Explicit fields must be provided, even if they can be inferred.
-/
namespace Ex7

structure S where
  n : Nat
  m : Fin n

variable (x : Fin 3)

/--
error: fields missing: 'n'

field 'n' must be explicitly provided, synthesized value is
  3
---
info: { n := 3, m := x } : S
-/
#guard_msgs in #check { m := x : S }

/-- info: { n := 3, m := x } : S -/
#guard_msgs in #check { n := _, m := x : S }

/-- info: { n := 3, m := x } : S -/
#guard_msgs in #check { m := x, .. : S }

/-- info: { n := 3, m := x } : S -/
#guard_msgs in #check { n := 3, m := x : S }

end Ex7

/-!
Diamond inheritance, acquire field values from parent classes.
https://github.com/leanprover/lean4/issues/6046
-/
namespace Issue6046
set_option structure.strictResolutionOrder true

class A

class B extends A where
  b : Unit

structure B' where
  b : Unit

class C extends B', B, A

instance : A where

instance : B where
  b := ()

instance : C where

/--
info: def Issue6046.instC : C :=
{ b := B.b }
-/
#guard_msgs in #print Issue6046.instC

end Issue6046
