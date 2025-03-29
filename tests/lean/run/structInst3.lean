
universe u

set_option pp.structureInstanceTypes true

namespace Ex1

structure A (α : Type u) where
  (x : α) (f : α → α := λ x => x)

structure B (α : Type u) extends A α where
  (y : α := f (f x)) (g : α → α → α := λ x y => f x)

structure C (α : Type u) extends B α where
  (z : α := g x y) (x := f z)

end Ex1

open Ex1

def c1 : C Nat := { x := 1 }

/--
info: let __src := c1;
{ toB := __src.toB, z := 2 : C Nat } : C Nat
-/
#guard_msgs in #check { c1 with z := 2 }

theorem ex1 : { c1 with z := 2 }.z = 2 :=
rfl

/--
info: ex1 :
  (let __src := c1;
      { toB := __src.toB, z := 2 : C Nat }).z =
    2
-/
#guard_msgs in #check ex1

theorem ex2 : { c1 with z := 2 }.x = c1.x :=
rfl

/--
info: ex2 :
  (let __src := c1;
      { toB := __src.toB, z := 2 : C Nat }).x =
    c1.x
-/
#guard_msgs in #check ex2

def c2 : C (Nat × Nat) := { z := (1, 1) }

/--
info: let __src := c2;
{
  x :=
    let __src := __src.x;
    (2, __src.snd),
  f := __src.f, y := __src.y, g := __src.g, z := __src.z : C (Nat × Nat) } : C (Nat × Nat)
-/
#guard_msgs in #check { c2 with x.fst := 2 }

/--
info: let __src := c2;
{
  x :=
    let __src := __src.x;
    (3, __src.snd),
  f := __src.f, y := __src.y, g := __src.g, z := __src.z : C (Nat × Nat) } : C (Nat × Nat)
-/
#guard_msgs in #check { c2 with x.1 := 3 }

/--
info: let_fun this :=
  let __src := c2.toB;
  { toB := __src, z := __src.g __src.x __src.y : C (Nat × Nat) };
this : C (Nat × Nat)
-/
#guard_msgs in #check show C _ from { c2.toB with .. }
