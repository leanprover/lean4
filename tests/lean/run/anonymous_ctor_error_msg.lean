

structure Foo := (n : Nat)

def Foo.sum (xs : List Foo) : Foo :=
xs.foldl (λ s x => ⟨s.n + x.n⟩) ⟨0⟩

#check
let x1 := ⟨1⟩
let x2 := ⟨2⟩
let x3 := ⟨3⟩
-- let x4 := ⟨4⟩; -- If this line is uncommented we get the error at `⟨`
let x5 := ⟨5⟩
let x6 := ⟨6⟩
Foo.sum [x1, x2, x3, x5, x6]
