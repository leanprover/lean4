import data.nat
open nat

inductive fn2 (A B C : Type) :=
mk : (A → C) → (B → C) → fn2 A B C

definition to_ac [coercion] {A B C : Type} (f : fn2 A B C) : A → C :=
fn2.rec (λ f g, f) f

definition to_bc [coercion] {A B C : Type} (f : fn2 A B C) : B → C :=
fn2.rec (λ f g, g) f

constant f : fn2 Prop nat nat
constant a : Prop
constant n : nat
check f a
check f n
