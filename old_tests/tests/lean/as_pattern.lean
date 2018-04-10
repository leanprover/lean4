namespace as_pattern
inductive foo
| a | b | c

inductive bar : foo → Type
| a : bar foo.a
| b : bar foo.b

def basic : list foo → list foo
| x@([_])      := x -- `@[` starts an attribute
| x@_          := x
#print prefix as_pattern.basic.equations

def nested : list foo → list foo
| (x@foo.b :: _) := [x]
| x              := x
#print prefix as_pattern.nested.equations

def value : option ℕ → option ℕ
| (some x@2) := some x
| x          := x
#print prefix as_pattern.value.equations

def weird_but_ok : ℕ → ℕ
| x@y@z := x+y+z
#print prefix as_pattern.weird_but_ok.equations

def too_many : ℕ → ℕ
| x@_ := x
| x@0 := x
| x@_ := x
| x   := x

def too_many2 : ℕ → ℕ
| x@x@0 := x
| x@x   := x

def dependent : Π (f : foo), bar f → foo
| x@foo.a bar.a := x
| x@_     bar.b := x
#print prefix as_pattern.dependent.equations

section involved
universe variables u v
inductive imf {A : Type u} {B : Type v} (f : A → B) : B → Type (max 1 u v)
| mk : ∀ (a : A), imf (f a)

definition inv_1 {A : Type u} {B : Type v} (f : A → B) : ∀ (b : B), imf f b → A
| x@.(f w) y@(imf.mk z@.(f) w@a) := w
end involved

def unicode : ℕ → ℕ
| n₁@_ := n₁
end as_pattern
