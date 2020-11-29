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

unif_hint (s : Magma) where
  s =?= Nat.Magma |- s.α =?= Nat

unif_hint (s : Magma) (m : Magma) (n : Magma) (β : Type u) (δ : Type v) where
  m.α =?= β
  n.α =?= δ
  s =?= Prod.Magma m n
  |-
  s.α =?= β × δ

def f1 (x : Nat) : Nat :=
  mul x x

#eval f1 10

def f2 (x y : Nat) : Nat × Nat :=
  mul (x, y) (x, y)

#eval f2 10 20

def f3 (x y : Nat) : Nat × Nat × Nat :=
  mul (x, y, y) (x, y, y)

#eval f3 7 24
