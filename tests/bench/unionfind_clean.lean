abbreviation Node := Nat

structure nodeData :=
(find : Node) (rank : Nat := 0)

abbreviation ufData := Array nodeData

abbreviation M (α : Type) := EState String ufData α

def capacity : M Nat :=
do d ← get; pure d.size

def findEntryAux : Nat → Node → M nodeData
| 0     n := throw "out of fuel"
| (i+1) n :=
  do s ← get;
     if h : n < s.size then
       do { let e := s.fget ⟨n, h⟩;
            if e.find = n then pure e
            else do e₁ ← findEntryAux i e.find;
                    modify (fun s => s.set n e₁);
                    pure e₁ }
     else throw "invalid Node"

def findEntry (n : Node) : M nodeData :=
do c ← capacity;
   findEntryAux c n

def find (n : Node) : M Node :=
do e ← findEntry n; pure e.find

def mk : M Node :=
do n ← capacity;
   modify $ fun s => s.push {find := n, rank := 1};
   pure n

def union (n₁ n₂ : Node) : M Unit :=
do r₁ ← findEntry n₁;
   r₂ ← findEntry n₂;
   if r₁.find = r₂.find then pure ()
   else modify $ fun s =>
     if r₁.rank < r₂.rank then s.set r₁.find { find := r₂.find }
     else if r₁.rank = r₂.rank then
        let s₁ := s.set r₁.find { find := r₂.find } in
        s₁.set r₂.find { rank := r₂.rank + 1, .. r₂}
     else s.set r₂.find { find := r₁.find }


def mkNodes : Nat → M Unit
| 0     := pure ()
| (n+1) := mk *> mkNodes n

def checkEq (n₁ n₂ : Node) : M Unit :=
do r₁ ← find n₁; r₂ ← find n₂;
   unless (r₁ = r₂) $ throw "nodes are not equal"

def mergePackAux : Nat → Nat → Nat → M Unit
| 0     _ _ := pure ()
| (i+1) n d :=
  do c ← capacity;
  if (n+d) < c
  then union n (n+d) *> mergePackAux i (n+1) d
  else pure ()

def mergePack (d : Nat) : M Unit :=
do c ← capacity; mergePackAux c 0 d

def numEqsAux : Nat → Node → Nat → M Nat
| 0     _ r := pure r
| (i+1) n r :=
  do c ← capacity;
     if n < c
     then do { n₁ ← find n; numEqsAux i (n+1) (if n = n₁ then r else r+1) }
     else pure r

def numEqs : M Nat :=
do c ← capacity;
   numEqsAux c 0 0

def test (n : Nat) : M Nat :=
if n < 2 then throw "input must be greater than 1"
else do
  mkNodes n;
  mergePack 50000;
  mergePack 10000;
  mergePack 5000;
  mergePack 1000;
  numEqs

def main (xs : List String) : IO UInt32 :=
let n := xs.head.toNat in
match (test n).run Array.empty with
| EState.Result.ok v s    => IO.println ("ok " ++ toString v) *> pure 0
| EState.Result.error e s => IO.println ("Error : " ++ e) *> pure 1
