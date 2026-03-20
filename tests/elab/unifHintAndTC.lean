structure Magma where
  carrier   : Type u
  mul : carrier → carrier → carrier

instance : CoeSort Magma (Type u) where
  coe m := m.carrier

def mul {s : Magma} (a b : s) : s :=
  s.mul a b

infixl:70 (priority := high) " * " => mul

example {S : Magma} (a b c : S) : b = c → a * b = a * c := by
  intro h; rw [h]

def Nat.Magma : Magma where
  carrier := Nat
  mul a b := Nat.mul a b

unif_hint (s : Magma) where
  s =?= Nat.Magma |- s.carrier =?= Nat

example (x : Nat) : Nat :=
  x * x

def Prod.Magma (m : Magma) (n : Magma) : Magma where
  carrier := m.carrier × n.carrier
  mul a b := (a.1 * b.1, a.2 * b.2)

unif_hint (s : Magma) (m : Magma) (n : Magma) (β : Type u) (δ : Type v) where
  m.carrier =?= β
  n.carrier =?= δ
  s =?= Prod.Magma m n
  |-
  s.carrier =?= β × δ

def f2 (x y : Nat) : Nat × Nat :=
  (x, y) * (x, y)

#eval f2 10 20

def f3 (x y : Nat) : Nat × Nat × Nat :=
  (x, y, y) * (x, y, y)

#eval f3 7 24

def magmaOfMul (α : Type u) [Mul α] : Magma where -- Bridge between `Mul α` and `Magma`
  carrier := α
  mul a b := Mul.mul a b

unif_hint (s : Magma) (α : Type u) [Mul α] where
  s =?= magmaOfMul α
  |-
  s.carrier =?= α

def g (x y : Int) : Int :=
  x * y -- Note that we don't have a hint connecting Magma's carrier and Int

set_option pp.all true
#print g -- magmaOfMul is used

def h (x y : UInt32) : UInt32 :=
  let f z w := z * w * z
  f x y
