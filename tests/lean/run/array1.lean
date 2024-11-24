#check @Array.mk

def v : Array Nat := Array.mk [1, 2, 3, 4]

def w : Array Nat :=
(mkArray 9 1).push 3

#check @Array.casesOn

def f : Fin w.size → Nat :=
  fun i => w.get i i.isLt

def arraySum (a : Array Nat) : Nat :=
a.foldl Nat.add 0

#guard mkArray 4 1 == #[1, 1, 1, 1]

#guard Array.map (fun x => x+10) v == #[11, 12, 13, 14]

#guard f ⟨1, sorry⟩ == 1

#guard f ⟨9, sorry⟩ == 3

#guard (((mkArray 1 1).push 2).push 3).foldl (fun x y => x + y) 0 == 6

#guard arraySum (mkArray 10 1) == 10

axiom axLt {a b : Nat} : a < b


#guard #[1, 2, 3].insertAt 0 10 == #[10, 1, 2, 3]
#guard #[1, 2, 3].insertAt 1 10 == #[1, 10, 2, 3]
#guard #[1, 2, 3].insertAt 2 10 == #[1, 2, 10, 3]
#guard #[1, 2, 3].insertAt 3 10 == #[1, 2, 3, 10]
#guard #[].insertAt 0 10 == #[10]

def tst1 : IO Unit :=
#[1, 2, 3, 4].forRevM IO.println

/--
info: 4
3
2
1
-/
#guard_msgs in
#eval tst1

#guard #[1, 2].extract 0 1 == #[1]
#guard #[1, 2].extract 0 0 == #[]
#guard #[1, 2].extract 0 2 == #[1, 2]

#guard #[1, 2, 3, 4].filterMap (fun x => if x % 2 == 0 then some (x + 10) else none) == #[12, 14]

def tst : IO (List Nat) :=
[1, 2, 3, 4].filterMapM fun x => do
  IO.println x;
  (if x % 2 == 0 then pure $ some (x + 10) else pure none)

/--
info: 1
2
3
4
---
info: [12, 14]
-/
#guard_msgs in
#eval tst

#guard #[1, 3, 6, 2].getMax? (fun a b => a < b) == some 6
#guard #[].getMax? (fun (a b : Nat) => a < b) == none
#guard #[1, 8].getMax? (fun a b => a < b) == some 8
#guard #[8, 1].getMax? (fun a b => a < b) == some 8

#guard #[1, 6, 5, 3, 8, 2, 0].partition (fun x => x % 2 == 0) == (#[6, 8, 2, 0], #[1, 5, 3])

def check (b : Bool) : IO Unit :=
unless b do throw $ IO.userError "check failed"

#guard #[].isPrefixOf #[2, 3]
#guard (#[] : Array Nat).isPrefixOf #[]
#guard #[2, 3].isPrefixOf #[2, 3]
#guard #[2, 3].isPrefixOf #[2, 3, 4, 5]
#guard ! #[2, 4].isPrefixOf #[2, 3]
#guard ! #[2, 3, 4].isPrefixOf #[2, 3]
#guard ! #[2].isPrefixOf #[]
#guard ! #[4, 3].isPrefixOf #[2, 3, 4, 5]

#guard #[1, 2, 3].allDiff
#guard !#[1, 2, 1, 3].allDiff
#guard #[1, 2, 4, 3].allDiff
#guard (#[] : Array Nat).allDiff
#guard !#[1, 1].allDiff
#guard !#[1, 2, 3, 4, 5, 1].allDiff
#guard #[1, 2, 3, 4, 5].allDiff
#guard !#[1, 2, 3, 4, 5, 5].allDiff
#guard !#[1, 3, 3, 4, 5].allDiff
#guard !#[1, 2, 3, 4, 5, 3].allDiff
#guard !#[1, 2, 3, 4, 5, 4].allDiff
#guard #[1, 2, 3, 4, 5, 6].allDiff

#guard Array.zip #[1, 2] #[3, 4, 6] == #[(1, 3), (2, 4)]

theorem ex1 (a b c : Nat) : #[a, b].push c = #[a, 0, c].set! 1 b :=
  rfl
