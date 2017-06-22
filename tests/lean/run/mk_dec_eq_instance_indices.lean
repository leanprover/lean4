open tactic

namespace X1

inductive Foo : unit -> Type
| mk : Foo () -> Foo ()

instance (u : unit) : decidable_eq (Foo u) := by mk_dec_eq_instance

end X1

namespace X2

inductive Foo : bool -> bool -> Type
| mk₁ : Foo tt tt
| mk₂ : Foo ff ff -> Foo tt ff

instance (idx₁ idx₂ : bool) : decidable_eq (Foo idx₁ idx₂) := by mk_dec_eq_instance

end X2

namespace X3

constants (C : nat -> Type)
constants (c : Pi (n : nat), C n)

inductive Foo : Pi (n : nat), C n -> Type
| mk₁ : Pi (n : nat), Foo n (c n) -> Foo (n+1) (c (n+1))
| mk₂ : Foo 0 (c 0)

noncomputable instance (n : nat) (c : C n) : decidable_eq (Foo n c) := by mk_dec_eq_instance

end X3

namespace X4

inductive Foo
| mk (n : nat) (val : fin n)

def fin_decidable (n) : decidable_eq (fin n) :=
by mk_dec_eq_instance

def dep_decidable : decidable_eq Foo :=
by mk_dec_eq_instance

end X4
