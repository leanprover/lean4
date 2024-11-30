/-!
# Tests for structure instance notation
-/

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

/-- info: { x := 1, y := 1 + 2, z := 2 * (1 + 2) } : C -/
#guard_msgs in #check { x := 1 : C }
/-- info: { x := 2 * 1 + 2, y := 1, z := 2 * 1 } : C -/
#guard_msgs in #check { y := 1 : C }
/-- info: { x := 1 + 2, y := 1 + 3, z := 1 } : C -/
#guard_msgs in #check { z := 1 : C }

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
Nested `where`
-/
namespace Ex6

structure A where
  x : Nat
structure B where
  a : A
  y : Nat

/-- info: { a := { x := 3 }, y := 0 } : B -/
#guard_msgs in #check {
  a where
    x := 3
  y := 0
  : B
}

def test1 : B where
  a where
    x := 3
  y := 0

def test2 : B where
  a.x := 3
  y := 0

end Ex6
