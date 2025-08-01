structure Magma.{u} where
  α   : Type u
  mul : α → α → α

def Nat.Magma : Magma where
  α       := Nat
  mul a b := a * b

def Prod.Magma (m : Magma.{u}) (n : Magma.{v}) : Magma where
  α  := m.α × n.α
  mul | (a₁, b₁), (a₂, b₂) => (m.mul a₁ a₂, n.mul b₁ b₂)

instance : CoeSort Magma.{u} (Type u) where
  coe m := m.α

def mul {s : Magma} (a b : s) : s :=
  s.mul a b

namespace Algebra

scoped unif_hint (s : Magma) where
  s =?= Nat.Magma |- s.α =?= Nat

end Algebra

set_option pp.mvars false

def x : Nat := 10

/--
error: Application type mismatch: The argument
  x
has type
  Nat
but is expected to have type
  Magma.α ?_
in the application
  mul ?_ x
-/
#guard_msgs in
#check mul x x           -- Error: unification hint is not active

/--
error: Application type mismatch: The argument
  (x, x)
has type
  Nat × Nat
but is expected to have type
  Magma.α ?_
in the application
  mul ?_ (x, x)
-/
#guard_msgs in
#check mul (x, x) (x, x) -- Error: no unification hint

local infix:65 (priority := high) "*" => mul

/--
error: Application type mismatch: The argument
  x
has type
  Nat
but is expected to have type
  Magma.α ?_
in the application
  ?_*x
-/
#guard_msgs in
#check x*x -- Error: unification hint is not active

open Algebra -- activate unification hints

#check mul x x -- works
#check x*x -- works

/--
error: Application type mismatch: The argument
  (x, x)
has type
  Nat × Nat
but is expected to have type
  Magma.α ?_
in the application
  ?_*(x, x)
-/
#guard_msgs in
#check mul (x, x) (x, x) -- still error

section Sec1

-- set_option trace.Meta.debug true
-- This hint is only active in this section
local unif_hint (s : Magma) (m : Magma) (n : Magma) (β : Type u) (δ : Type v) where
  m.α =?= β
  n.α =?= δ
  s =?= Prod.Magma m n
  |-
  s.α =?= β × δ

#check (x, x) * (x, x) -- works

end Sec1

/--
error: Application type mismatch: The argument
  (x, x)
has type
  Nat × Nat
but is expected to have type
  Magma.α ?_
in the application
  ?_*(x, x)
-/
#guard_msgs in
#check (x, x) * (x, x) -- error, local hint is not active after end of section anymore
