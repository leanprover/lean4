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

example (x : Unit × α) : x = ((), x.2) := rfl

example (x : (_ : True ∨ False) ×' α) : x = ⟨Or.inl ⟨⟩, x.2⟩ := rfl

example (p : α × α → Prop) (h : ∀ x y, p (x, y)) : p z := h z.1 _

class TopologicalSpace (α : Type)

structure Homeomorph (α β : Type) [TopologicalSpace α] [TopologicalSpace β] extends Equiv α β where
  continuousToFun : True
  continuousInv : True

def Homeomorph.symm [TopologicalSpace α] [TopologicalSpace β] (f : Homeomorph α β) : Homeomorph β α where
  toFun           := f.invFun
  invFun          := f.toFun
  left_inv        := sorry
  right_inv       := sorry
  continuousToFun := f.continuousInv
  continuousInv   := sorry

example [TopologicalSpace α] [TopologicalSpace β] (f : Homeomorph α β) :
  f.symm.symm = f := rfl -- fails

def frob : Nat × Nat → Nat × Nat
  | (x, y) => (x + y, 42)

example (x : Nat × Nat) : (frob x).2 = 42 := rfl

example (x y : Unit) : x = y := rfl

opaque f : Nat → Unit
opaque g : Nat → Unit

example (x y : Nat) : f x = f y := rfl

example (x y : Nat) : f x = g y := rfl
