section
parameters {A : Type} (R : list A → Prop)
structure foo (x : list A) : Prop := (bar : R x)
structure bar (x : Type)
structure baz extends bar A
end
