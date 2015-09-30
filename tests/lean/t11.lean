prelude constant A    : Type.{1}
definition bool : Type.{1} := Type.{0}
constant Exists (P : A → bool) : bool
notation `exists` binders `, ` b:(scoped b, Exists b) := b
notation `∃` binders `, ` b:(scoped b, Exists b) := b
constant p : A → bool
constant q : A → A → bool
check exists x : A, p x
check ∃ x y : A, q x y
notation `{` binder `|` b:scoped `}` := b
check {x : A | x}
