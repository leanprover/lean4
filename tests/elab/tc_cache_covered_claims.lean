/-!
Locks the extension-classification audit of the type class resolution dependency tracking: any
resolution-path read of an unclassified environment extension panics unconditionally (see
`Lean.EnvExtension.trackGen`). The file elaborates representative content whose searches
traverse the covered extensions: structures and classes (structure info, class table,
projection functions), instances with out-params, matchers and equation realization (matcher
info, eqns, match eqns), reducibility reads and post-hoc changes (declaration change log), and
auxiliary recursors. A panic here means the search path reached an extension that should
either be registered as covered (`synthCovered`, with a justification) or generation-tracked
and read through the recording accessors.
-/

structure Pt where
  x : Nat
  y : Nat

class Dist (α : Type) where
  dist : α → α → Nat

instance : Dist Pt := ⟨fun a b => (a.x - b.x) + (a.y - b.y) + (b.x - a.x) + (b.y - a.y)⟩

structure Pt3 extends Pt where
  z : Nat

instance : Dist Pt3 := ⟨fun a b => Dist.dist a.toPt b.toPt + (a.z - b.z) + (b.z - a.z)⟩

def d3 (a b : Pt3) : Nat := Dist.dist a b

class Sz (α : Type) (β : outParam Type) where
  sz : α → β

instance : Sz (List α) Nat := ⟨List.length⟩

example (l : List Nat) : Nat := Sz.sz l + d3 ⟨⟨1, 2⟩, 3⟩ ⟨⟨4, 5⟩, 6⟩

-- Matcher creation and equation realization inside proofs.
def classify : List Nat → Nat
  | [] => 0
  | [x] => x
  | _ :: _ :: _ => 2

example : classify [] = 0 := by simp [classify]
example : classify [7] = 7 := by simp [classify]
example (x y : Nat) (l : List Nat) : classify (x :: y :: l) = 2 := by simp [classify]

-- Structural recursion (def height overrides) and generated equations.
def sumUp : Nat → Nat
  | 0 => 0
  | n + 1 => n + 1 + sumUp n

example : sumUp 3 = 6 := by simp [sumUp]

-- Reducibility: a definition guarding an instance, then a post-hoc change observed by a query.
def Wrapped := Nat

example : (inferInstance : Dist Pt).dist ⟨0, 0⟩ ⟨1, 1⟩ = 2 := rfl

attribute [reducible] Wrapped

instance : Dist Wrapped := ⟨fun a b => (a : Nat) + (b : Nat)⟩

example : Dist.dist (2 : Wrapped) (3 : Wrapped) = 5 := rfl

-- Auxiliary recursors and noConfusion on an inductive family.
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α

def Tree.size : Tree α → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

instance : Dist (Tree Nat) := ⟨fun a b => a.size + b.size⟩

example (t : Tree Nat) : Dist.dist t t = 2 * t.size := by
  simp [Dist.dist, Nat.two_mul]
