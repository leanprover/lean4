inductive Tree
  | nil
  | node (l r : Tree)
instance : Inhabited Tree := ⟨.nil⟩

-- This function has an extra argument to suppress the
-- common sub-expression elimination optimization
partial def make' (n d : UInt32) : Tree :=
  if d = 0 then .node .nil .nil
  else .node (make' n (d - 1)) (make' (n + 1) (d - 1))

-- build a tree
def make (d : UInt32) := make' d d

def check : Tree → UInt32
  | .nil => 0
  | .node l r => 1 + check l + check r

def minN := 4

def out (s : String) (n : Nat) (t : UInt32) : IO Unit :=
  IO.println s!"{s} of depth {n}\t check: {t}"

-- allocate and check lots of trees
partial def sumT (d i t : UInt32) : UInt32 :=
  if i = 0 then t
  else
    let a := check (make d)
    sumT d (i-1) (t + a)

-- generate many trees
partial def depth (d m : Nat) : List (Nat × Nat × Task UInt32) :=
  if d ≤ m then
    let n := 2 ^ (m - d + minN)
    (n, d, Task.spawn (fun _ => sumT (.ofNat d) (.ofNat n) 0)) :: depth (d+2) m
  else []

def main : List String → IO UInt32
  | [s] => do
    let n := s.toNat!
    let maxN := Nat.max (minN + 2) n
    let stretchN := maxN + 1

    -- stretch memory tree
    let c := check (make $ UInt32.ofNat stretchN)
    out "stretch tree" stretchN c

    -- allocate a long lived tree
    let long := make $ UInt32.ofNat maxN

    -- allocate, walk, and deallocate many bottom-up binary trees
    let vs := (depth minN maxN)  -- `using` (parList $ evalTuple3 r0 r0 rseq)
    vs.forM (fun (m, d, i) => out s!"{m}\t trees" d i.get)

    -- confirm the long-lived binary tree still exists
    out "long lived tree" maxN (check long)
    return 0
  | _ => return 1
