
universe u

namespace Ex1

structure A (α : Type u) :=
(x : α) (f : α → α := λ x => x)

structure B (α : Type u) extends A α :=
(y : α := f (f x)) (g : α → α → α := λ x y => f x)

structure C (α : Type u) extends B α :=
(z : α := g x y) (x := f z)

end Ex1

open Ex1

def c1 : C Nat := { x := 1 }

#check { c1 with z := 2 }

#check { c1 with z := 2 }

theorem ex1 : { c1 with z := 2 }.z = 2 :=
rfl

#check ex1

theorem ex2 : { c1 with z := 2 }.x = c1.x :=
rfl

#check ex2

def c2 : C (Nat × Nat) := { z := (1, 1) }

#check { c2 with x.fst := 2 }

#check { c2 with x.1 := 3 }
