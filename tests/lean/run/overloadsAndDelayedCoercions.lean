universe u

inductive Vector' (α : Type u) : Nat → Type u
  | nil : Vector' α 0
  | cons : {n : Nat} → α → Vector' α n → Vector' α (n+1)

infix:67 " :: " => Vector'.cons

inductive Ty where
  | int
  | bool
  | fn (a r : Ty)

inductive HasType' : {n : Nat} → Vector' Ty n → Type where
  | stop {ty : Ty} : HasType' (ty :: ctx)

inductive HasType : Fin n → Vector' Ty n → Ty → Type where
  | stop : HasType 0 (ty :: ctx) ty
  | pop  : HasType k ctx ty → HasType k.succ (u :: ctx) ty
