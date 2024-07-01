import Lean.Elab.Command

mutual
inductive A
  | self : A → A
  | other : B → A
  | empty
inductive B
  | self : B → B
  | other : A → B
  | empty
end

-- A simple mutually recursive function definition

mutual
def A.size : A → Nat
  | .self a => a.size + 1
  | .other b => b.size + 1
  | .empty => 0
termination_by structurally x => x
def B.size : B → Nat
  | .self b => b.size + 1
  | .other a => a.size + 1
  | .empty => 0
termination_by structurally x => x
end

-- And indeed all equationals hold definitionally

theorem A_size_eq1 (a : A) : (A.self a).size = a.size + 1 := rfl
theorem A_size_eq2 (b : B) : (A.other b).size = b.size + 1 := rfl
theorem A_size_eq3 : A.empty.size = 0  := rfl
theorem B_size_eq1 (b : B) : (B.self b).size = b.size + 1 := rfl
theorem B_size_eq2 (a : A) : (B.other a).size = a.size + 1 := rfl
theorem B_size_eq3 : B.empty.size = 0  := rfl

-- The expected equational theorems are produced

/-- info: A.size.eq_1 (a : A) : a.self.size = a.size + 1 -/
#guard_msgs in
#check A.size.eq_1

/-- info: A.size.eq_2 (b : B) : (A.other b).size = b.size + 1 -/
#guard_msgs in
#check A.size.eq_2

/-- info: A.size.eq_3 : A.empty.size = 0 -/
#guard_msgs in
#check A.size.eq_3

/-- info: B.size.eq_1 (b : B) : b.self.size = b.size + 1 -/
#guard_msgs in
#check B.size.eq_1

/-- info: B.size.eq_2 (a : A) : (B.other a).size = a.size + 1 -/
#guard_msgs in
#check B.size.eq_2

/-- info: B.size.eq_3 : B.empty.size = 0 -/
#guard_msgs in
#check B.size.eq_3

-- Smart unfolding works

/--
info: a : A
h : (B.other a).size = 1
⊢ a.size = 0
-/
#guard_msgs in
theorem ex1 (a : A) (h : (A.other (B.other a)).size = 2) : a.size = 0 := by
  injection h with h
  trace_state -- without smart unfolding the state would be a mess
  injection h with h


-- And it computes in type just fine

mutual
def A.subs : (a : A) → (Fin a.size → A ⊕ B)
  | .self a => Fin.lastCases (.inl a) (a.subs)
  | .other b => Fin.lastCases (.inr b) (b.subs)
  | .empty => Fin.elim0
termination_by structurally x => x
def B.subs : (b : B) → (Fin b.size → A ⊕ B)
  | .self b => Fin.lastCases (.inr b) (b.subs)
  | .other a => Fin.lastCases (.inl a) (a.subs)
  | .empty => Fin.elim0
termination_by structurally x => x
end


-- We can define mutually recursive theorems as well

mutual
def A.hasNoBEmpty : A → Prop
  | .self a => a.hasNoBEmpty
  | .other b => b.hasNoBEmpty
  | .empty => True
termination_by structurally x => x
def B.hasNoBEmpty : B → Prop
  | .self b => b.hasNoBEmpty
  | .other a => a.hasNoBEmpty
  | .empty => False
termination_by structurally x => x
end

-- Mixing Prop and Nat.
-- This works because both `Prop` and `Nat` are in the same universe (`Type`)

mutual
open Classical
noncomputable
def A.hasNoAEmpty : A → Prop
  | .self a => a.hasNoAEmpty
  | .other b => b.oddCount > 0
  | .empty => False
termination_by structurally x => x
noncomputable
def B.oddCount : B → Nat
  | .self b => b.oddCount + 1
  | .other a => if a.hasNoAEmpty then 0 else 1
  | .empty => 0
termination_by structurally x => x
end

-- Higher levels, but the same level `Type u`

mutual
open Classical
def A.type.{u} : A → Type u
  | .self a => Unit × a.type
  | .other b => Unit × b.type
  | .empty => PUnit
termination_by structurally x => x
def B.type.{u} : B → Type u
  | .self b => PUnit × b.type
  | .other a => PUnit × a.type
  | .empty => PUnit
termination_by structurally x => x
end


-- Mixed levels, should error

/--
error: invalid mutual definition, result types must be in the same universe level, resulting type for `A.strangeType` is
  Type : Type 1
and for `B.odderCount` is
  Nat : Type
-/
#guard_msgs in
mutual
open Classical
def A.strangeType : A → Type
  | .self a => Unit × a.strangeType
  | .other b => Fin b.odderCount
  | .empty => Unit
termination_by structurally x => x
def B.odderCount : B → Nat
  | .self b => b.odderCount + 1
  | .other a => if Nonempty a.strangeType then 0 else 1
  | .empty => 0
termination_by structurally x => x
end


namespace Index

/-! An example where the data type has parameters and indices -/

mutual
inductive A (m : Nat) : Nat → Type
  | self : A m n → A m (n+m)
  | other : B m n → A m (n+m)
  | empty : A m 0
inductive B (m : Nat) : Nat → Type
  | self : B m n → B m (n+m)
  | other : A m n → B m (n+m)
  | empty : B m 0
end

mutual
def A.size (m n : Nat) : A m n → Nat
  | .self a => a.size + m
  | .other b => b.size + m
  | .empty => 0
termination_by structurally x => x
def B.size (m n : Nat): B m n → Nat
  | .self b => b.size + m
  | .other a => a.size + m
  | .empty => 0
termination_by structurally x => x
end

mutual
theorem A.size_eq_index (m n : Nat) : (a : A m n) → a.size = n
  | .self a => by dsimp [A.size]; rw[ A.size_eq_index]
  | .other b => by dsimp [A.size]; rw [B.size_eq_index]
  | .empty => rfl
termination_by structurally x => x
theorem B.size_eq_index (m n : Nat) : (b : B m n) → b.size = n
  | .self b => by dsimp [B.size]; rw [B.size_eq_index]
  | .other a => by dsimp [B.size]; rw [A.size_eq_index]
  | .empty => rfl
termination_by structurally x => x
end

end Index


namespace EvenOdd

-- Mutual structural recursion over a non-mutual inductive type

mutual
  def isEven : Nat → Prop
    | 0 => True
    | n+1 => ¬ isOdd n
  termination_by structurally x => x

  def isOdd : Nat → Prop
    | 0 => False
    | n+1 => ¬ isEven n
  termination_by structurally x => x
end

end EvenOdd

namespace MutualIndNonMutualFun

mutual
inductive A
  | self : A → A
  | other : B → A
  | empty
inductive B
  | self : B → B
  | other : A → B
  | empty
end

-- Structural recursion ignoring some types of the mutual inductive

def A.self_size : A → Nat
  | .self a => a.self_size + 1
  | .other _ => 0
  | .empty => 0
termination_by structurally x => x

#guard_msgs in
def B.self_size : B → Nat
  | .self b => b.self_size + 1
  | .other _ => 0
  | .empty => 0
termination_by structurally x => x

-- Structural recursion with more than one function per types of the mutual inductive

mutual
def A.weird_size1 : A → Nat
  | .self a => a.weird_size2 + 1
  | .other _ => 0
  | .empty => 0
termination_by structurally x => x
def A.weird_size2 : A → Nat
  | .self a => a.weird_size3 + 1
  | .other _ => 0
  | .empty => 0
termination_by structurally x => x
def A.weird_size3 : A → Nat
  | .self a => a.weird_size1 + 1
  | .other _ => 0
  | .empty => 0
termination_by structurally x => x
end

end MutualIndNonMutualFun

namespace NestedWithTuple

inductive Tree where
  | leaf
  | node : (Tree × Tree) → Tree

def Tree.below_1 (motive : Tree → Sort u) : Tree → Sort (max 1 u) :=
  @Tree.below motive (fun _tt => PUnit)

-- Assume we had this construction:
@[reducible] protected noncomputable def Tree.brecOn.{u}
  {motive : Tree → Sort u}
  (t : Tree)
  (F : (t : Tree) → Tree.below_1 motive t → motive t) :
  motive t :=
  let motive_below := fun t => PProd (motive t) (Tree.below_1 motive t)
  (@Tree.rec
    motive_below
    -- This is the hypthetical `Pair_Tree.below tt` unfolded
    (fun ⟨t₁,t₂⟩ => PProd PUnit.{u} (PProd (motive_below t₁) (PProd (motive_below t₂) PUnit)))
    ⟨F Tree.leaf PUnit.unit, PUnit.unit⟩
    (fun ⟨a₁,a₂⟩ a_ih => ⟨F (Tree.node ⟨a₁, a₂⟩) ⟨a_ih, PUnit.unit⟩, ⟨a_ih, PUnit.unit⟩⟩)
    (fun _a _a_1 a_ih a_ih_1 => ⟨PUnit.unit, ⟨a_ih, ⟨a_ih_1, PUnit.unit⟩⟩⟩)
    t).1

-- Then the decrecursifier works just fine! (and FunInd too, see below)
#guard_msgs in
def Tree.size : Tree → Nat
  | leaf => 0
  | node (t₁, t₂) => t₁.size + t₂.size
termination_by structurally t => t

/--
info: theorem NestedWithTuple.Tree.size.eq_2 : ∀ (t₁ t₂ : Tree), (Tree.node (t₁, t₂)).size = t₁.size + t₂.size :=
fun t₁ t₂ => Eq.refl (Tree.node (t₁, t₂)).size
-/
#guard_msgs in
#print Tree.size.eq_2

end NestedWithTuple


namespace DifferentTypes

-- Check error message when argument types are not mutually recursive

inductive A
  | self : A → A
  | empty

/--
error: Cannot use structural mutual recursion: The recursive argument of DifferentTypes.A.with_nat is of type DifferentTypes.A, the recursive argument of DifferentTypes.Nat.foo is of type Nat, and these are not mutually recursive.
-/
#guard_msgs in
mutual
def A.with_nat : A → Nat
  | .self a => a.with_nat + Nat.foo 1
  | .empty => 0
termination_by structurally x => x
def Nat.foo : Nat → Nat
  | n+1 => Nat.foo n
  | 0 => A.empty.with_nat
termination_by structurally x => x
end

end DifferentTypes

namespace FixedIndex

/- Do we run into problems if one of the indices is part of the “fixed prefix”? -/

inductive T : Nat → Type
  | a : T 37
  | b : T n → T n

def T.size (n : Nat) (start : Nat) : T n → Nat
  | a => start
  | b t => 1 + T.size n start t
termination_by structurally t => t

namespace Mutual
mutual
def T.size1 (n : Nat) (start : Nat) : T n → Nat
  | .a => 0
  | .b t => 1 + T.size2 n start t
termination_by structurally t => t

def T.size2 (n : Nat) (start : Nat) : T n → Nat
  | .a => 0
  | .b t => 1 + T.size1 n start t
termination_by structurally t => t
end

end Mutual

/--
error: its type FixedIndex.T is an inductive family and indices are not variables
  T 37
-/
#guard_msgs in
def T.size2 : T 37 → Nat
  | a => 0
  | b t => 1 + T.size2 t
termination_by structurally t => t

end FixedIndex


namespace FunIndTests

-- FunInd does not handle mutual structural recursion yet, so make sure we error
-- out nicely

/--
error: Failed to realize constant A.size.induct:
  functional induction: cannot handle mutual inductives
---
error: Failed to realize constant A.size.induct:
  functional induction: cannot handle mutual inductives
---
error: unknown identifier 'A.size.induct'
-/
#guard_msgs in
#check A.size.induct

/--
error: Failed to realize constant A.subs.induct:
  functional induction: cannot handle mutual inductives
---
error: Failed to realize constant A.subs.induct:
  functional induction: cannot handle mutual inductives
---
error: unknown identifier 'A.subs.induct'
-/
#guard_msgs in
#check A.subs.induct

/--
error: Failed to realize constant MutualIndNonMutualFun.A.self_size.induct:
  functional induction: cannot handle mutual inductives
---
error: Failed to realize constant MutualIndNonMutualFun.A.self_size.induct:
  functional induction: cannot handle mutual inductives
---
error: unknown identifier 'MutualIndNonMutualFun.A.self_size.induct'
-/
#guard_msgs in
#check MutualIndNonMutualFun.A.self_size.induct

/--
error: Failed to realize constant A.hasNoBEmpty.induct:
  functional induction: cannot handle mutual inductives
---
error: Failed to realize constant A.hasNoBEmpty.induct:
  functional induction: cannot handle mutual inductives
---
error: unknown identifier 'A.hasNoBEmpty.induct'
-/
#guard_msgs in
#check A.hasNoBEmpty.induct

/--
error: Failed to realize constant EvenOdd.isEven.induct:
  Function EvenOdd.isEven does not look like a function defined by recursion.
  NB: If EvenOdd.isEven is not itself recursive, but contains an inner recursive function (via `let rec` or `where`), try `EvenOdd.isEven.go` where `go` is name of the inner function.
---
error: Failed to realize constant EvenOdd.isEven.induct:
  Function EvenOdd.isEven does not look like a function defined by recursion.
  NB: If EvenOdd.isEven is not itself recursive, but contains an inner recursive function (via `let rec` or `where`), try `EvenOdd.isEven.go` where `go` is name of the inner function.
---
error: unknown identifier 'EvenOdd.isEven.induct'
-/
#guard_msgs in
#check EvenOdd.isEven.induct -- TODO: This error message can be improved


-- For Tree.size this would actually work already:

run_meta
  Lean.modifyEnv fun env => Lean.markAuxRecursor env ``NestedWithTuple.Tree.brecOn

/--
info: NestedWithTuple.Tree.size.induct (motive : NestedWithTuple.Tree → Prop) (case1 : motive NestedWithTuple.Tree.leaf)
  (case2 : ∀ (t₁ t₂ : NestedWithTuple.Tree), motive t₁ → motive t₂ → motive (NestedWithTuple.Tree.node (t₁, t₂))) :
  ∀ (a : NestedWithTuple.Tree), motive a
-/
#guard_msgs in
#check NestedWithTuple.Tree.size.induct

end FunIndTests
