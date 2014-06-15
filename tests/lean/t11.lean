variable A    : Type.{1}
definition bool : Type.{1} := Type.{0}
variable Exists (P : A → bool) : bool
notation `exists` binders `,` b:(scoped b, Exists b) := b
notation `∃` binders `,` b:(scoped b, Exists b) := b
variable p : A → bool
variable q : A → A → bool
check exists x : A, p x
check ∃ x y : A, q x y
notation `{` binder `|` b:scoped `}` := b
check {x : A | x}
