open tactic

namespace X1

inductive Wrap (A : Type) : Type
| mk : A -> Wrap

inductive Foo : Type
| mk : Wrap Foo -> Foo

instance : decidable_eq Foo := by mk_dec_eq_instance

end X1

namespace X2

inductive Foo : Type
| mk : list Foo -> Foo

instance : decidable_eq Foo := by mk_dec_eq_instance

end X2

namespace X3

inductive Foo : bool -> Type
| mk : list (list (Foo tt)) -> Foo ff

instance (b : bool) : decidable_eq (Foo b) := by mk_dec_eq_instance

end X3
