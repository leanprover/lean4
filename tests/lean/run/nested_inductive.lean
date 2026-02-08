
/-! # Nested inductive types

See "Recursion through lists and arrays" in https://blog.lean-lang.org/blog/2024-9-1-lean-4110/

This test file exercises the `attach`/`unattach` API.
-/

namespace List

inductive Tree where | node : List Tree → Tree

namespace Tree

def rev : Tree → Tree
  | node ts => .node (ts.attach.reverse.map (fun ⟨t, _⟩ => t.rev))

-- Note that `simp` now automatically removes the `attach`.
@[simp] theorem rev_def (ts : List Tree) :
    Tree.rev (.node ts) = .node (ts.reverse.map rev) := by
  simp [Tree.rev]

-- Variant with an explicit `have`, rather than using a pattern match.
def rev' : Tree → Tree
  | node ts => .node (ts.attach.reverse.map (fun t => have := t.2; t.1.rev'))

@[simp] theorem rev'_def (ts : List Tree) :
    Tree.rev' (.node ts) = .node (ts.reverse.map rev') := by
  simp [Tree.rev']

/-- Define `size` using a `foldl` over `attach`. -/
def size : Tree → Nat
  | node ts => 1 + ts.attach.foldl (fun acc ⟨t, _⟩ => acc + t.size) 0

@[simp] theorem size_def (ts : List Tree) :
    size (.node ts) = 1 + ts.foldl (fun acc t => acc + t.size) 0 := by
  simp [size]

/-- Define `depth` using a `foldr` over `attach`. -/
def depth : Tree → Nat
  | node ts => 1 + ts.attach.foldr (fun ⟨t, _⟩ acc => acc + t.depth) 0

@[simp] theorem depth_def (ts : List Tree) :
    depth (.node ts) = 1 + ts.foldr (fun t acc => acc + t.depth) 0 := by
  simp [depth]

end Tree

end List

namespace Array

inductive Tree where | node : Array Tree → Tree

namespace Tree

def rev : Tree → Tree
  | node ts => .node (ts.attach.reverse.map (fun ⟨t, _⟩ => t.rev))

-- Note that `simp` now automatically removes the `attach`.
@[simp] theorem rev_def (ts : Array Tree) :
    Tree.rev (.node ts) = .node (ts.reverse.map rev) := by
  simp [Tree.rev]

/-- Define `size` using a `foldl` over `attach`. -/
def size : Tree → Nat
  | node ts => 1 + ts.attach.foldl (fun acc ⟨t, _⟩ => acc + t.size) 0

@[simp] theorem size_def (ts : Array Tree) :
    size (.node ts) = 1 + ts.foldl (fun acc t => acc + t.size) 0 := by
  simp [size]

/-- Define `depth` using a `foldr` over `attach`. -/
def depth : Tree → Nat
  | node ts => 1 + ts.attach.foldr (fun ⟨t, _⟩ acc => acc + t.depth) 0

@[simp] theorem depth_def (ts : Array Tree) :
    depth (.node ts) = 1 + ts.foldr (fun t acc => acc + t.depth) 0 := by
  simp [depth]

end Tree

end Array


namespace Option

inductive Tree where | node : Option Tree → Option Tree → Tree

namespace Tree

def rev : Tree → Tree
  | node l r => .node (r.attach.map fun ⟨r, _⟩ => r.rev) (l.attach.map fun ⟨l, _⟩ => l.rev)

@[simp] theorem rev_def (l r : Option Tree) :
    Tree.rev (.node l r) = .node (r.map rev) (l.map rev) := by
  simp [Tree.rev]

end Tree

end Option
