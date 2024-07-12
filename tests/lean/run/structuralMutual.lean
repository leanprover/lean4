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
termination_by structural x => x
def B.size : B → Nat
  | .self b => b.size + 1
  | .other a => a.size + 1
  | .empty => 0
termination_by structural x => x
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
termination_by structural x => x
def B.subs : (b : B) → (Fin b.size → A ⊕ B)
  | .self b => Fin.lastCases (.inr b) (b.subs)
  | .other a => Fin.lastCases (.inl a) (a.subs)
  | .empty => Fin.elim0
termination_by structural x => x
end


-- We can define mutually recursive theorems as well

mutual
def A.hasNoBEmpty : A → Prop
  | .self a => a.hasNoBEmpty
  | .other b => b.hasNoBEmpty
  | .empty => True
termination_by structural x => x
def B.hasNoBEmpty : B → Prop
  | .self b => b.hasNoBEmpty
  | .other a => a.hasNoBEmpty
  | .empty => False
termination_by structural x => x
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
termination_by structural x => x
noncomputable
def B.oddCount : B → Nat
  | .self b => b.oddCount + 1
  | .other a => if a.hasNoAEmpty then 0 else 1
  | .empty => 0
termination_by structural x => x
end

-- Higher levels, but the same level `Type u`

mutual
open Classical
def A.type.{u} : A → Type u
  | .self a => Unit × a.type
  | .other b => Unit × b.type
  | .empty => PUnit
termination_by structural x => x
def B.type.{u} : B → Type u
  | .self b => PUnit × b.type
  | .other a => PUnit × a.type
  | .empty => PUnit
termination_by structural x => x
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
termination_by structural x => x
def B.odderCount : B → Nat
  | .self b => b.odderCount + 1
  | .other a => if Nonempty a.strangeType then 0 else 1
  | .empty => 0
termination_by structural x => x
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
termination_by structural x => x
def B.size (m n : Nat): B m n → Nat
  | .self b => b.size + m
  | .other a => a.size + m
  | .empty => 0
termination_by structural x => x
end

mutual
theorem A.size_eq_index (m n : Nat) : (a : A m n) → a.size = n
  | .self a => by dsimp [A.size]; rw[ A.size_eq_index]
  | .other b => by dsimp [A.size]; rw [B.size_eq_index]
  | .empty => rfl
termination_by structural x => x
theorem B.size_eq_index (m n : Nat) : (b : B m n) → b.size = n
  | .self b => by dsimp [B.size]; rw [B.size_eq_index]
  | .other a => by dsimp [B.size]; rw [A.size_eq_index]
  | .empty => rfl
termination_by structural x => x
end

end Index


namespace EvenOdd

-- Mutual structural recursion over a non-mutual inductive type

mutual
  def Even : Nat → Prop
    | 0 => True
    | n+1 => ¬ Odd n
  termination_by structural x => x

  def Odd : Nat → Prop
    | 0 => False
    | n+1 => ¬ Even n
  termination_by structural x => x
end

mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => ! isOdd n
  termination_by structural x => x

  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => ! isEven n
  termination_by structural x => x
end

theorem isEven_eq_2 (n : Nat) : isEven (n+1) = ! isOdd n := rfl

/-- info: EvenOdd.isEven.eq_1 : isEven 0 = true -/
#guard_msgs in
#check isEven.eq_1

theorem eq_true_of_not_eq_false {b : Bool} : (! b) = false → b = true := by simp
theorem eq_false_of_not_eq_true {b : Bool} : (! b) = true → b = false := by simp

/--
info: n : Nat
h : EvenOdd.isOdd (n + 1) = false
⊢ EvenOdd.isEven n = true
-/
#guard_msgs in
theorem ex1 (n : Nat) (h : isEven (n+2) = true) : isEven n = true := by
  replace h := eq_false_of_not_eq_true h
  trace_state -- without smart unfolding the state would be a mess
  replace h := eq_true_of_not_eq_false h
  exact h

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
termination_by structural x => x

#guard_msgs in
def B.self_size : B → Nat
  | .self b => b.self_size + 1
  | .other _ => 0
  | .empty => 0
termination_by structural x => x

-- Structural recursion with more than one function per types of the mutual inductive

mutual
def A.weird_size1 : A → Nat
  | .self a => a.weird_size2 + 1
  | .other _ => 0
  | .empty => 0
termination_by structural x => x
def A.weird_size2 : A → Nat
  | .self a => a.weird_size3 + 1
  | .other _ => 0
  | .empty => 0
termination_by structural x => x
def A.weird_size3 : A → Nat
  | .self a => a.weird_size1 + 1
  | .other _ => 0
  | .empty => 0
termination_by structural x => x
end

-- We have equality
theorem A.weird_size1_eq_1 (a : A) : (A.self a).weird_size1 = a.weird_size2 + 1 := rfl

-- And the right equational theorems
/--
info: MutualIndNonMutualFun.A.weird_size1.eq_1 (a : A) : a.self.weird_size1 = a.weird_size2 + 1
-/
#guard_msgs in
#check A.weird_size1.eq_1

end MutualIndNonMutualFun

namespace NestedWithTuple

inductive Tree where
  | leaf
  | node : (Tree × Tree) → Tree

-- Nested recursion does not work (yet)

/-- error: its type NestedWithTuple.Tree is a nested inductive, which is not yet supported -/
#guard_msgs in
def Tree.size : Tree → Nat
  | leaf => 0
  | node (t₁, t₂) => t₁.size + t₂.size
termination_by structural t => t

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
termination_by structural x => x
def Nat.foo : Nat → Nat
  | n+1 => Nat.foo n
  | 0 => A.empty.with_nat
termination_by structural x => x
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
termination_by structural t => t

namespace Mutual
mutual
def T.size1 (n : Nat) (start : Nat) : T n → Nat
  | .a => 0
  | .b t => 1 + T.size2 n start t
termination_by structural t => t

def T.size2 (n : Nat) (start : Nat) : T n → Nat
  | .a => 0
  | .b t => 1 + T.size1 n start t
termination_by structural t => t
end

end Mutual

namespace Mutual2

mutual
inductive  A : Nat → Type
  | a : A n
  | b : B → A n → A n
inductive  B : Type
  | a : ((n : Nat) → A n) → B
end

-- In this test A and B have `n start` as fixed prefix, but only
-- in `A` the `n` is an index

set_option linter.constructorNameAsVariable false in
mutual
def A.size (n : Nat) (start : Nat) : A n → Nat
  | .a => 0
  | .b b a => 1 + B.size n start b + A.size n start a
termination_by structural t => t

def B.size (n : Nat) (start : Nat) : B → Nat
  | .a a => 1 + A.size n start (a n)
termination_by structural t => t
end

end Mutual2

namespace Mutual3

mutual
inductive  A (n : Nat) : Type
  | a : A n
  | b : B n → A n
inductive  B (n : Nat) : Type
  | a : A n → B n
end

/--
error: its type is an inductive datatype
  A n
and the datatype parameter
  n
depends on the function parameter
  n
which does not come before the varying parameters and before the indices of the recursion parameter.
-/
#guard_msgs in
set_option linter.constructorNameAsVariable false in
mutual
def A.size (n : Nat) (m : Nat) : A n → Nat
  | .a => 0
  | .b b => 1 + B.size m n b
termination_by structural t => t

def B.size (n : Nat) (m : Nat) : B m → Nat
  | .a a => 1 + A.size m n a
termination_by structural t => t
end

end Mutual3

/--
error: its type FixedIndex.T is an inductive family and indices are not variables
  T 37
-/
#guard_msgs in
def T.size2 : T 37 → Nat
  | a => 0
  | b t => 1 + T.size2 t
termination_by structural t => t

end FixedIndex

namespace IndexIsParameter

-- Not actual mutual, but since I was at it

inductive T (n : Nat) : Nat → Type where
  | z : T n n
  | n : T n n → T n n

/--
error: its type is an inductive datatype
  T n n
and the datatype parameter
  n
depends on the function parameter
  n
which does not come before the varying parameters and before the indices of the recursion parameter.
-/
#guard_msgs in
def T.a (n : Nat) : T n n → Nat
  | .z => 0
  | .n t => t.a + 1
termination_by structural t => t


end IndexIsParameter


namespace DifferentParameters

-- An attempt to make it fall over mutual recursion over the same type
-- but with different parameters.

inductive T (n : Nat) : Type where
  | z : T n
  | n : T n → T n

/--
error: The inductive type of the recursive parameter of DifferentParameters.T.a and DifferentParameters.T.b have different parameters:
  [23]
  [42]
-/
#guard_msgs in
mutual
def T.a : T 23 → Nat
  | .z => 0
  | .n t => t.a + 1 + T.b .z
termination_by structural t => t
def T.b : T 42 → Nat
  | .z => 0
  | .n t => t.b + 1 + T.a .z
termination_by structural t => t
end

end DifferentParameters

namespace FunIndTests

-- FunInd does not handle mutual structural recursion yet, so make sure we error
-- out nicely

/--
error: Failed to realize constant A.size.induct:
  functional induction: cannot handle mutual or nested inductives
---
error: Failed to realize constant A.size.induct:
  functional induction: cannot handle mutual or nested inductives
---
error: unknown identifier 'A.size.induct'
-/
#guard_msgs in
#check A.size.induct

/--
error: Failed to realize constant A.subs.induct:
  functional induction: cannot handle mutual or nested inductives
---
error: Failed to realize constant A.subs.induct:
  functional induction: cannot handle mutual or nested inductives
---
error: unknown identifier 'A.subs.induct'
-/
#guard_msgs in
#check A.subs.induct

/--
error: Failed to realize constant MutualIndNonMutualFun.A.self_size.induct:
  functional induction: cannot handle mutual or nested inductives
---
error: Failed to realize constant MutualIndNonMutualFun.A.self_size.induct:
  functional induction: cannot handle mutual or nested inductives
---
error: unknown identifier 'MutualIndNonMutualFun.A.self_size.induct'
-/
#guard_msgs in
#check MutualIndNonMutualFun.A.self_size.induct

/--
error: Failed to realize constant A.hasNoBEmpty.induct:
  functional induction: cannot handle mutual or nested inductives
---
error: Failed to realize constant A.hasNoBEmpty.induct:
  functional induction: cannot handle mutual or nested inductives
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

end FunIndTests
