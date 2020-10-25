

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

set_option pp.all true

#check myFun 3       -- works
#check @myFun Nat 3  -- works

#check myFun' _ 3    -- works
#check myFun' Nat 3  -- works

variable (c : ConstantFunction Nat Nat)
#check c 3 -- works

#check (fun c => c 3) myFun -- works
