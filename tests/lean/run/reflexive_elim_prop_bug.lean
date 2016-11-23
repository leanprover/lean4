namespace tst1

inductive Foo : Type
| node : (ℕ → Foo) → Foo
| leaf : Foo

constant Bar : Type
constant P : Bar → Prop
constant Q : Bar → Type
axiom P_ax : ∀ b, P b

lemma foo_error : ∀ (foo : Foo) (b : Bar), P b
| (Foo.node f) := λ b, foo_error (f 0) b
| Foo.leaf     := λ b, P_ax b

end tst1

namespace tst2

inductive Foo : Type
| node : (ℕ → Foo) → Foo

constant Bar : Type
constant P : Bar → Prop
constant Q : Bar → Type

lemma foo_error : ∀ (foo : Foo) (b : Bar), P b
| (Foo.node f) := λ b, foo_error (f 0) b

end tst2
