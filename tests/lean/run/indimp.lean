prelude
definition Prop := Type.{0}

inductive nat :=
| zero : nat
| succ : nat → nat

inductive list (A : Type) :=
| nil {} : list A
| cons   : A → list A → list A

inductive list2 (A : Type) : Type :=
| nil2 {} : list2 A
| cons2   : A → list2 A → list2 A

inductive and (A B : Prop) : Prop :=
and_intro : A → B → and A B

inductive cls {T1 : Type} (R1 : T1 → T1 → Prop) {T2 : Type} (R2 : T2 → T2 → Prop) (f : T1 → T2) :=
mk : (∀x y : T1, R1 x y → R2 (f x) (f y)) → cls R1 R2 f
