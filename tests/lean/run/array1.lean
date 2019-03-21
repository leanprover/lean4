#check @Array.mk

#eval mkArray 4 1

def v : Array Nat := @Array.mk Nat 10 (λ ⟨i, _⟩, i)

#eval Array.map (+10) v

def w : Array Nat :=
(mkArray 9 1).push 3

def f : Fin w.sz → Nat :=
Array.casesOn w (λ _ f, f)

#eval f ⟨1, sorry⟩
#eval f ⟨9, sorry⟩

#eval (((mkArray 1 1).push 2).push 3).foldl 0 (+)

def arraySum (a : Array Nat) : Nat :=
a.foldl 0 (+)

#eval arraySum (mkArray 10 1)

#exit

#eval (mkArray 10 1).data ⟨1, decTrivial⟩ + 20
#eval (mkArray 10 1).data ⟨2, decTrivial⟩
#eval (mkArray 10 3).data ⟨2, decTrivial⟩
