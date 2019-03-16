inductive Tree
| Nil
| Node (l r : Tree) : Tree
open Tree

-- This function has an extra argument to suppress the
-- Common Sub-expression Elimination optimization
def make' : uint32 -> uint32 -> Tree
| n d :=
  if d = 0 then Node Nil Nil
  else Node (make' n (d - 1)) (make' (n + 1) (d - 1))

-- build a tree
def make (d : uint32) := make' d d

def check : Tree → uint32
| Nil := 0
| (Node l r) := 1 + check l + check r

def minN := 4

def out (s) (n : nat) (t : uint32) := io.println (s ++ " of depth " ++ to_string n ++ "\t check: " ++ to_string t)

-- allocate and check lots of trees
def sumT : uint32 -> uint32 -> uint32 -> uint32
| d i t :=
  if i = 0 then t
  else
    let a := check (make d) in
    sumT d (i-1) (t + a)

-- generate many trees
meta def depth : nat -> nat -> list (nat × nat × task uint32)
| d m := if d ≤ m then
    let n := 2 ^ (m - d + minN) in
    (n, d, task.mk (λ _, sumT (uint32.of_nat d) (uint32.of_nat n) 0)) :: depth (d+2) m
  else []

meta def main : list string → io uint32
| [s] := do
  let n := s.to_nat,
  let maxN := nat.max (minN + 2) n,
  let stretchN := maxN + 1,

  -- stretch memory tree
  let c := check (make $ uint32.of_nat stretchN),
  out "stretch tree" stretchN c,

  -- allocate a long lived tree
  let long := make $ uint32.of_nat maxN,

  -- allocate, walk, and deallocate many bottom-up binary trees
  let vs := (depth minN maxN), -- `using` (parList $ evalTuple3 r0 r0 rseq)
  vs.mmap (λ ⟨m,d,i⟩, out (to_string m ++ "\t trees") d i.get),

  -- confirm the the long-lived binary tree still exists
  out "long lived tree" maxN (check long),
  pure 0
| _ := pure 1
