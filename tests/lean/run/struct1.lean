

structure A0.{u} (α : Type u) :=
(x : α)

structure A.{u} (α : Type u) extends A0 α :=
(y : α)

structure B.{u} (α : Type u) :=
(z : α)

variable (β : Type _)
variable (β' : Type _)

universe u

structure C.{v} (α : Type _) (δ : Type u) (η : Type v) extends A β, B α :=
mk2 :: (w : Nat := 10)

#check C
#check @C
#check @C.mk2
#check { x := 10, y := 20, z := 30, w := 40 : C Nat Nat Nat Nat }
#check C.recOn
#check C.w
#check fun (c : C Nat Nat Nat Nat) => c.x

def f0 (c : C Nat Nat Nat Nat) : A Nat :=
c.toA

def f1 (c : C Nat Nat Nat Nat) :=
c.x + c.w

class Tst (α : Type u) extends Mul α :=
(comm : ∀ (a b : α), a * b = b * a)

#check @Tst.comm
#check @Tst.toMul

def foo {α} [Tst α] (a b : α) :=
a * b

#check { x := 10, y := 20, z := 30 : C Nat Nat Nat Nat }

class Foo (α : Type u) extends Add α :=
(x : α)

class Boo (α : Type u) extends Foo α :=
(y : α := x + x)

#check @Boo.y._default

#check { add := Nat.add, x := 10 : Boo Nat}
