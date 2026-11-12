section
universe u
variable (A : Type u)
class abbrev AddAbbrev := Add A
end

section
universe v
variable {A : Sort v}
class Bar (A : Sort u) (f : A -> Prop) where (bar : (a : A) -> f a)
class abbrev BarAbbrev (f : A -> Prop) := Bar A f
end

section
universe u
class Foo (A : Sort u) (f : A -> Prop) where (foo : (a : A) -> f a)
class abbrev FooAbbrev {A : Sort u} (f : A -> Prop) := Foo A f
end
