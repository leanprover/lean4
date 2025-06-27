structure Foo where (n : Nat)
def Foo.f1 (f : Foo) : Nat := f.n
def Foo.f2 (f : Foo) : Nat := f.n
def Foo.f3 (f : Foo) : Nat := f.n
def Foo.f4 (f : Foo) : Nat := f.n
def Foo.f5 (f : Foo) : Nat := f.n

/--
error: Invalid field notation: Type of
  f
is not known; cannot resolve field `n`
---
error: Invalid field notation: Type of
  g
is not known; cannot resolve field `n`
---
error: Invalid field notation: Type of
  f
is not known; cannot resolve field `f1`
---
error: Invalid field notation: Type of
  g
is not known; cannot resolve field `f2`
---
error: Invalid field notation: Type of
  h
is not known; cannot resolve field `f3`
---
error: Invalid field notation: Type of
  f
is not known; cannot resolve field `f4`
---
error: Invalid field notation: Type of
  g
is not known; cannot resolve field `f5`
---
error: Invalid field notation: Type of
  h
is not known; cannot resolve field `f6`
-/
#guard_msgs in
example := (λ f g h =>
  let x : Foo := ⟨f.n + 1⟩;
  let y : Foo := ⟨g.n + 1⟩;
  (λ f g h => f.f1 + g.f2 + h.f3 + f.f4 + g.f5 + h.f6) f g h)

/--
error: Invalid field notation: Type of
  id x
is not known; cannot resolve field `foo`
-/
#guard_msgs in
example := fun x => (id x).foo
