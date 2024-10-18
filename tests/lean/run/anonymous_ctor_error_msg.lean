set_option pp.mvars false

structure Foo := (n : Nat)

def Foo.sum (xs : List Foo) : Foo :=
xs.foldl (λ s x => ⟨s.n + x.n⟩) ⟨0⟩

/--
info: let x1 := { n := 1 };
let x2 := { n := 2 };
let x3 := { n := 3 };
let x5 := { n := 5 };
let x6 := { n := 6 };
Foo.sum [x1, x2, x3, x5, x6] : Foo
-/
#guard_msgs in
#check
let x1 := ⟨1⟩
let x2 := ⟨2⟩
let x3 := ⟨3⟩
-- let x4 := ⟨4⟩; -- If this line is uncommented we get the error at `⟨`
let x5 := ⟨5⟩
let x6 := ⟨6⟩
Foo.sum [x1, x2, x3, x5, x6]

/--
error: invalid constructor ⟨...⟩, expected type must be an inductive type ⏎
  ?_
---
info: let x1 := { n := 1 };
let x2 := { n := 2 };
let x3 := { n := 3 };
let x4 := ?_;
let x5 := { n := 5 };
let x6 := { n := 6 };
Foo.sum [x1, x2, x3, x5, x6] : Foo
-/
#guard_msgs in
#check
let x1 := ⟨1⟩
let x2 := ⟨2⟩
let x3 := ⟨3⟩
let x4 := ⟨4⟩; -- If this line is uncommented we get the error at `⟨`
let x5 := ⟨5⟩
let x6 := ⟨6⟩
Foo.sum [x1, x2, x3, x5, x6]
