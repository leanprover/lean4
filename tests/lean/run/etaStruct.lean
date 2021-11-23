example (x : α × β) : x = (x.1, x.2) :=
  rfl -- Should work with eta for structures

example (x : Unit) : x = ⟨⟩ :=
  rfl -- Should work with eta for structures

structure Equiv (α : Sort u) (β : Sort v) where
  toFun    : α → β
  invFun   : β → α
  left_inv  : ∀ x, invFun (toFun x) = x
  right_inv : ∀ x, toFun (invFun x) = x

infix:50 "≃" => Equiv

def Equiv.symm (e : α ≃ β) : β ≃ α :=
  { toFun     := e.invFun
    invFun    := e.toFun
    left_inv  := e.right_inv
    right_inv := e.left_inv }

theorem Equiv.symm.symm (e : α ≃ β) : e.symm.symm = e :=
  rfl -- Should work with eta for structures

structure Bla where
  x : Nat

def Bla.toNat (b : Bla) : Nat := b.x
def Nat.toBla (x : Nat) : Bla := { x }

example (b : Bla) : b.toNat.toBla = b :=
  rfl -- Should work with eta for structures

example (b : Bla) : b.toNat.toBla = b := by
  cases b
  rfl
