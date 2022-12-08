inductive Fam : Type → Type 1 where
  | any : Fam α
  | nat : Nat → Fam Nat

example (a : α) : Fam α → α
  | Fam.any => a
  | Fam.nat n => n

inductive Fam2 : Type → Type → Type 1 where
  | any : Fam2 α α
  | nat : Nat → Fam2 Nat Nat

example (a : α) : Fam2 α β → β
  | Fam2.any   => a
  | Fam2.nat n => n
