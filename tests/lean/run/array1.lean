#check @Array.mk

def v : Array Nat := Array.mk [1, 2, 3, 4]

def w : Array Nat :=
(mkArray 9 1).push 3

#check @Array.casesOn

def f : Fin w.size → Nat :=
  w.get

def arraySum (a : Array Nat) : Nat :=
a.foldl Nat.add 0

#eval mkArray 4 1
#eval Array.map (fun x => x+10) v
#eval f ⟨1, sorry⟩
#eval f ⟨9, sorry⟩
#eval (((mkArray 1 1).push 2).push 3).foldl (fun x y => x + y) 0
#eval arraySum (mkArray 10 1)
axiom axLt {a b : Nat} : a < b


#eval #[1, 2, 3].insertAt 0 10
#eval #[1, 2, 3].insertAt 1 10
#eval #[1, 2, 3].insertAt 2 10
#eval #[1, 2, 3].insertAt 3 10
#eval #[].insertAt 0 10

def tst1 : IO Unit :=
#[1, 2, 3, 4].forRevM IO.println

#eval tst1

#eval #[1, 2].extract 0 1
#eval #[1, 2].extract 0 0
#eval #[1, 2].extract 0 2

#eval #[1, 2, 3, 4].filterMap fun x => if x % 2 == 0 then some (x + 10) else none

def tst : IO (List Nat) :=
[1, 2, 3, 4].filterMapM fun x => do
  IO.println x;
  (if x % 2 == 0 then pure $ some (x + 10) else pure none)

#eval tst

#eval #[1, 3, 6, 2].getMax? (fun a b => a < b)
#eval #[].getMax? (fun (a b : Nat) => a < b)
#eval #[1, 8].getMax? (fun a b => a < b)
#eval #[8, 1].getMax? (fun a b => a < b)

#eval #[1, 6, 5, 3, 8, 2, 0].partition fun x => x % 2 == 0

def check (b : Bool) : IO Unit :=
unless b do throw $ IO.userError "check failed"

#eval check $ #[].isPrefixOf #[2, 3]
#eval check $ (#[] : Array Nat).isPrefixOf #[]
#eval check $ #[2, 3].isPrefixOf #[2, 3]
#eval check $ #[2, 3].isPrefixOf #[2, 3, 4, 5]
#eval check $ ! #[2, 4].isPrefixOf #[2, 3]
#eval check $ ! #[2, 3, 4].isPrefixOf #[2, 3]
#eval check $ ! #[2].isPrefixOf #[]
#eval check $ ! #[4, 3].isPrefixOf #[2, 3, 4, 5]

#eval check $ #[1, 2, 3].allDiff
#eval check $ !#[1, 2, 1, 3].allDiff
#eval check $ #[1, 2, 4, 3].allDiff
#eval check $ (#[] : Array Nat).allDiff
#eval check $ !#[1, 1].allDiff
#eval check $ !#[1, 2, 3, 4, 5, 1].allDiff
#eval check $ #[1, 2, 3, 4, 5].allDiff
#eval check $ !#[1, 2, 3, 4, 5, 5].allDiff
#eval check $ !#[1, 3, 3, 4, 5].allDiff
#eval check $ !#[1, 2, 3, 4, 5, 3].allDiff
#eval check $ !#[1, 2, 3, 4, 5, 4].allDiff
#eval check $ #[1, 2, 3, 4, 5, 6].allDiff

#eval check $ Array.zip #[1, 2] #[3, 4, 6] == #[(1, 3), (2, 4)]

theorem ex1 (a b c : Nat) : #[a, b].push c = #[a, 0, c].set! 1 b :=
  rfl
