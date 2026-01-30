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

Hint: Consider replacing the field projection with a call to one of the following:
  • `Foo.n`
  • `BitVec.DivModArgs.n`
---
error: Invalid field notation: Type of
  g
is not known; cannot resolve field `n`

Hint: Consider replacing the field projection with a call to one of the following:
  • `Foo.n`
  • `BitVec.DivModArgs.n`
---
error: Invalid field notation: Type of
  f
is not known; cannot resolve field `f1`

Hint: Consider replacing the field projection `.f1` with a call to the function `Foo.f1`.
---
error: Invalid field notation: Type of
  g
is not known; cannot resolve field `f2`

Hint: Consider replacing the field projection `.f2` with a call to the function `Foo.f2`.
---
error: Invalid field notation: Type of
  h
is not known; cannot resolve field `f3`

Hint: Consider replacing the field projection `.f3` with a call to the function `Foo.f3`.
---
error: Invalid field notation: Type of
  f
is not known; cannot resolve field `f4`

Hint: Consider replacing the field projection `.f4` with a call to the function `Foo.f4`.
---
error: Invalid field notation: Type of
  g
is not known; cannot resolve field `f5`

Hint: Consider replacing the field projection `.f5` with a call to the function `Foo.f5`.
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

/--
error: Invalid field notation: Type of
  x✝
is not known; cannot resolve field `isWhitespace`

Hint: Consider replacing the field projection `.isWhitespace` with a call to the function `Char.isWhitespace`.
-/
#guard_msgs in
example := (·.isWhitespace)

/--
error: Invalid field notation: Type of
  x
is not known; cannot resolve field `succ`

Hint: Consider replacing the field projection with a call to one of the following:
  • `Fin.succ`
  • `Nat.succ`
  • `Std.PRange.succ`
-/
#guard_msgs in
example := fun x => x.succ
