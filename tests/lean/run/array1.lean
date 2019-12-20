#check @Array.mk

def v : Array Nat := @Array.mk Nat 10 (fun ⟨i, _⟩ => i)

def w : Array Nat :=
(mkArray 9 1).push 3

def f : Fin w.sz → Nat :=
Array.casesOn w (fun _ f => f)

def arraySum (a : Array Nat) : Nat :=
a.foldl Nat.add 0

#eval mkArray 4 1
#eval Array.map (fun x => x+10) v
#eval f ⟨1, sorry⟩
#eval f ⟨9, sorry⟩
#eval (((mkArray 1 1).push 2).push 3).foldl (fun x y => x + y) 0
#eval arraySum (mkArray 10 1)
axiom axLt {a b : Nat} : a < b
#eval (mkArray 10 1).data ⟨1, axLt⟩ + 20
#eval (mkArray 10 1).data ⟨2, axLt⟩
#eval (mkArray 10 3).data ⟨2, axLt⟩

#eval #[1, 2, 3].insertAt 0 10
#eval #[1, 2, 3].insertAt 1 10
#eval #[1, 2, 3].insertAt 2 10
#eval #[1, 2, 3].insertAt 3 10
#eval #[].insertAt 0 10

def tst1 : IO Unit :=
#[1, 2, 3, 4].forRevM IO.println

#eval tst1
