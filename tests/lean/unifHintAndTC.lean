structure Magma.{u} where
  α   : Type u
  mul : α → α → α

instance : CoeSort Magma.{u} (Type u) where
  coe m := m.α

def mul {s : Magma} (a b : s) : s :=
  s.mul a b

infixl:70 (priority := high) "*" => mul

def Nat.Magma : Magma where
  α       := Nat
  mul a b := Nat.mul a b

def Prod.Magma (m : Magma.{u}) (n : Magma.{v}) : Magma where
  α  := m.α × n.α
  mul a b := (a.1 * b.1, a.2 * b.2)

unif_hint (s : Magma) where
  s =?= Nat.Magma |- s.α =?= Nat

unif_hint (s : Magma) (m : Magma) (n : Magma) (β : Type u) (δ : Type v) where
  m.α =?= β
  n.α =?= δ
  s =?= Prod.Magma m n
  |-
  s.α =?= β × δ

def f1 (x : Nat) : Nat :=
  x * x

#eval f1 10

def f2 (x y : Nat) : Nat × Nat :=
  (x, y) * (x, y)

#eval f2 10 20

def f3 (x y : Nat) : Nat × Nat × Nat :=
  (x, y, y) * (x, y, y)

#eval f3 7 24

def magmaOfMul (α : Type u) [Mul α] : Magma where -- Bridge between `Mul α` and `Magma`
  α       := α
  mul a b := Mul.mul a b

unif_hint (s : Magma) (α : Type u) [Mul α] where
  s =?= magmaOfMul α
  |-
  s.α =?= α

def g (x y : Int) : Int :=
  x * y -- Note that we don't have a hint connecting Magma's carrier and Int

set_option pp.all true
#print g -- magmaOfMul is used

def h (x y : UInt32) : UInt32 :=
  let f z w := z * w * z
  f x y
