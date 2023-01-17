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
    for d in [minN:maxN+1:2] do
      let n := 2 ^ (maxN - d + minN)
      let i := sumT (.ofNat d) (.ofNat n) 0
      out s!"{n}\t trees" d i

    -- confirm the long-lived binary tree still exists
    out "long lived tree" maxN (check long)
    return 0
  | _ => return 1
