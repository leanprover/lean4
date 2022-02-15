inductive Fam2 : Type → Type → Type 1 where
  | any : Fam2 α α
  | nat : Nat → Fam2 Nat Nat

example (a : α) (x : Fam2 α β) : β :=
  match α, β, a, x with
  | ?α, ?β, ?a, Fam2.any   => _
  | ?α, ?β, ?a, Fam2.nat n => _
