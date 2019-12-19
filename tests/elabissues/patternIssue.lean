inductive Moo : Type
| M1 : Moo
| M2 : Moo

inductive Foo : Type
| mk₁ : Moo → Foo
| mk₂ : Foo

def bar : Foo → String
| Foo.mk₁ M1 => "mk₁ M1"
| _ => "else"

#eval bar (Foo.mk₁ Moo.M2) -- "mk₁ M1"
