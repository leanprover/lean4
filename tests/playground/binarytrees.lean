inductive Tree
| Nil
| Node (l r : Tree) : Tree
open Tree

-- This function has an extra argument to suppress the
-- Common Sub-expression Elimination optimization
def make' : int -> nat -> Tree
| _ 0 := Node Nil Nil
| n (d+1) := Node (make' (n - 1) d) (make' (n + 1) d)

-- build a tree
def make (d : nat) := make' d d

def check : Tree → nat
| Nil := 0
| (Node l r) := 1 + check l + check r

def minN := 4

def out (s) (n t : nat) := io.println' (s ++ " of depth " ++ to_string n ++ "\t check: " ++ to_string t)

-- allocate and check lots of trees
def sumT : nat -> nat -> nat -> nat
| d 0 t := t
| d i t :=
  let a := check (make d) in
  sumT d (i-1) (t + a)

-- generate many trees
meta def depth : nat -> nat -> list (nat × nat × task nat)
| d m := if d ≤ m then
    let n := 2 ^ (m - d + minN) in
    (n, d, task.mk (λ _, sumT d n 0)) :: depth (d+2) m
  else []

meta def main : list string → io uint32
| [s] := do
  let n := s.to_nat,
  let maxN := nat.max (minN + 2) n,
  let stretchN := maxN + 1,

  -- stretch memory tree
  let c := check (make stretchN),
  out "stretch tree" stretchN c,

  -- allocate a long lived tree
  let long := make maxN,

  -- allocate, walk, and deallocate many bottom-up binary trees
  let vs := (depth minN maxN), -- `using` (parList $ evalTuple3 r0 r0 rseq)
  vs.mmap (λ ⟨m,d,i⟩, out (to_string m ++ "\t trees") d i.get),

  -- confirm the the long-lived binary tree still exists
  out "long lived tree" maxN (check long),
  pure 0
| _ := pure 1
