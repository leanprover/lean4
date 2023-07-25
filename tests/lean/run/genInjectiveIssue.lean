inductive WF : Nat → Type 1
  | mk (α : Type) (fn : α → Nat) (arg : α) : WF (fn arg)

inductive WF2 : Nat → Type 1
  | mk (α : Type) (fn : α → Nat) (arg : α) (n : Nat) : WF2 (fn arg)

#print WF2.mk.inj
