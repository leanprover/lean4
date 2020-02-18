/-
This is an annoyingly unhelpful error message that I see all the time.
An exact line number would help a lot, but even so it would be great
to replace the `⟨...⟩` with the actual term in question.

[Leo]: The bad position is due the transition to the new elaborator.
The new frontend produces the correct position.
Note that, the new frontend reports an error at `⟨4⟩`. This is the correct
position, and it is not possible to infer anything about the expected type since
`x4` is not used anywhere. So, the error message is the best we can get.
There is no actual term to replace. If we comment the line `let x4 := ...`,
the new elaborator succeeds.

-/
structure Foo := (n : Nat)

def Foo.sum (xs : List Foo) : Foo :=
xs.foldl (λ s x => ⟨s.n + x.n⟩) ⟨0⟩

#check
let x1 := ⟨1⟩;
let x2 := ⟨2⟩;
let x3 := ⟨3⟩;
let x4 := ⟨4⟩;
let x5 := ⟨5⟩;
let x6 := ⟨6⟩;
Foo.sum [x1, x2, x3, x5, x6]
/-
error: invalid constructor ⟨...⟩, expected type is not an inductive type
  ?m_1
-/
