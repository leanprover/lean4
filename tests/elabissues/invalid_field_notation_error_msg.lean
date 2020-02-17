/-
This is an annoyingly unhelpful error message that I see frequently.
It reports the prefix of the field notation, but not the field that we are trying to access.
An exact line number would help, but even so it would be great to report the field as well.
-/
structure Foo := (n : Nat)
def Foo.f1 (f : Foo) : Nat := f.n
def Foo.f2 (f : Foo) : Nat := f.n
def Foo.f3 (f : Foo) : Nat := f.n
def Foo.f4 (f : Foo) : Nat := f.n
def Foo.f5 (f : Foo) : Nat := f.n

#check (λ f g h =>
  let x : Foo := ⟨f.n + 1⟩;
  let y : Foo := ⟨g.n + 1⟩;
  (λ f g h => f.f1 + g.f2 + h.f3 + f.f4 + g.f5 + h.f6) f g h)
/-
/home/dselsam/omega/lean4/tests/elabissues/invalid_field_notation_error.lean:8:0: error: invalid field notation, type is not of the form (C ...) where C is a constant
-/
