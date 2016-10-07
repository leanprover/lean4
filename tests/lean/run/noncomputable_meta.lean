constants (X : Type) (x y : X)

noncomputable meta def foo : bool -> X
| tt := x
| ff := y
