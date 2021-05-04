section
universe u 
variable (A : Type u)
class abbrev AddAbbrev :=  Add A
end

section
universe u 
class Foo (A : Sort u) (f : A -> Prop) := (foo : (a : A) -> f a)
class abbrev FooAbbrev {A : Sort u} (f : A -> Prop) := Foo A f
end 

class abbrev FooAbbrev'.{U} {A : Sort U} (f : A -> Prop) := Foo A f

section
universe u 
variable {A : Sort u}
class Bar (A : Sort u) (f : A -> Prop) := (bar : (a : A) -> f a)
class abbrev BarAbbrev (f : A -> Prop) := Bar A f
end
