inductive Fam2 : Type → Type → Type 1 where
  | any : Fam2 α α
  | nat : Nat → Fam2 Nat Nat

set_option pp.rawOnError true
set_option trace.Elab.info true
example (a : α) (x : Fam2 α β) : β :=
  match x with
  | Fam2.any   => _
  | Fam2.nat n => n
