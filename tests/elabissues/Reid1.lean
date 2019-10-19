structure constantFunction (α β : Type) :=
(f : α → β)
(h : ∀ a₁ a₂, f a₁ = f a₂)

instance {α β : Type} : HasCoeToFun (constantFunction α β) :=
⟨_, constantFunction.f⟩

def myFun {α : Type} : constantFunction α (Option α) :=
{ f := fun a => none,
  h := fun a₁ a₂ => rfl }

def myFun' (α : Type) : constantFunction α (Option α) :=
{ f := fun a => none,
  h := fun a₁ a₂ => rfl }

#check myFun 3
#check @myFun Nat 3            -- works

#check myFun' _ 3
#check myFun' Nat 3            -- works

#check ⇑myFun 3
#check ⇑(myFun' _) 3
#check ⇑(myFun' Nat) 3
