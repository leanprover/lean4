#check @Array.mk

def v : Array Nat := @Array.mk Nat 10 (fun ⟨i, _⟩ => i)

def w : Array Nat :=
(mkArray 9 1).push 3

def f : Fin w.sz → Nat :=
Array.casesOn w (fun _ f => f)

def arraySum (a : Array Nat) : Nat :=
a.foldl Nat.add 0

#exit

#eval mkArray 4 1
#eval Array.map (+10) v
#eval f ⟨1, sorry⟩
#eval f ⟨9, sorry⟩
#eval (((mkArray 1 1).push 2).push 3).foldl 0 (+)
#eval arraySum (mkArray 10 1)
#eval (mkArray 10 1).data ⟨1, decTrivial⟩ + 20
#eval (mkArray 10 1).data ⟨2, decTrivial⟩
#eval (mkArray 10 3).data ⟨2, decTrivial⟩
