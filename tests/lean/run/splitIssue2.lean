namespace Batteries

/-- Union-find node type -/
structure UFNode where
  /-- Parent of node -/
  parent : Nat

namespace UnionFind

/-- Parent of a union-find node, defaults to self when the node is a root -/
def parentD (arr : Array UFNode) (i : Nat) : Nat :=
  if h : i < arr.size then (arr.get i h).parent else i

/-- Rank of a union-find node, defaults to 0 when the node is a root -/
def rankD (arr : Array UFNode) (i : Nat) : Nat := 0

theorem parentD_of_not_lt : ¬i < arr.size → parentD arr i = i := sorry

theorem parentD_set {arr : Array UFNode} {x h v i} :
    parentD (arr.set x v h) i = if x = i then v.parent else parentD arr i := by
  rw [parentD]
  sorry

end UnionFind

open UnionFind

structure UnionFind where
  arr : Array UFNode

namespace UnionFind

/-- Size of union-find structure. -/
@[inline] abbrev size (self : UnionFind) := self.arr.size

/-- Parent of union-find node -/
abbrev parent (self : UnionFind) (i : Nat) : Nat := parentD self.arr i

theorem parent_lt (self : UnionFind) (i : Nat) : self.parent i < self.size ↔ i < self.size :=
  sorry

/-- Rank of union-find node -/
abbrev rank (self : UnionFind) (i : Nat) : Nat := rankD self.arr i

/-- Maximum rank of nodes in a union-find structure -/
noncomputable def rankMax (self : UnionFind) := 0

/-- Root of a union-find node. -/
def root (self : UnionFind) (x : Fin self.size) : Fin self.size :=
  let y := (self.arr.get x.1 x.2).parent
  if h : y = x then
    x
  else
    have : self.rankMax - self.rank (self.arr.get x.1 x.2).parent < self.rankMax - self.rank x :=
      sorry
    self.root ⟨y, sorry⟩
termination_by self.rankMax - self.rank x

/-- Root of a union-find node. Returns input if index is out of bounds. -/
def rootD (self : UnionFind) (x : Nat) : Nat :=
  if h : x < self.size then self.root ⟨x, h⟩ else x

theorem rootD_parent (self : UnionFind) (x : Nat) : self.rootD (self.parent x) = self.rootD x := by
  simp only [rootD, Array.length_toList, parent_lt]
  split
  · simp only [parentD, ↓reduceDIte, *]
    conv => rhs; rw [root]
    split
    · rw [root, dif_pos] <;> simp_all
    · simp
  · simp only [not_false_eq_true, parentD_of_not_lt, *]
