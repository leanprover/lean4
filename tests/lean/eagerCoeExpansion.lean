def BV (n : Nat) := { b : Array Bool // b.size = n }

instance : Coe (BV 32) (Array Bool) where
  coe bv := bv.val

def f (x : BV n) := x

def g (x : Array Bool) := x

def h (x : BV 32) : Array Bool :=
  (fun x => g (f x)) x

#print h

def r (a : Nat) : Prop :=
  if a == 0 then (a != 1 : Prop) else a != 2

#print r

set_option pp.all true in
#print r

structure ConstantFunction (α β : Type) :=
(f : α → β)
(h : ∀ a₁ a₂, f a₁ = f a₂)

instance constFunCoe {α β : Type} : CoeFun (ConstantFunction α β) (fun _ => α → β) :=
{ coe := fun c => c.f }

def myFun {α : Type} : ConstantFunction α (Option α) :=
{ f := fun a => none,
  h := fun a₁ a₂ => rfl }

def myFun' (α : Type) : ConstantFunction α (Option α) :=
{ f := fun a => none,
  h := fun a₁ a₂ => rfl }

def s :=
  myFun 3 <|> myFun 4

#print s
