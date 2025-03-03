set_option guard_msgs.diff true

/-!
Mutual structural recursion.

In this file, we often attach a `termination_by structural` annotation to at least
one of the functions to force structural recursion. We don't want lean to resort to
well-founded recursion if structural recursion fails somehow.
-/

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
def A.size {m n : Nat} : A m n → Nat
  | .self a => a.size + m
  | .other b => b.size + m
  | .empty => 0
termination_by structural x => x
def B.size {m n : Nat} : B m n → Nat
  | .self b => b.size + m
  | .other a => a.size + m
  | .empty => 0
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
end

end Index


namespace EvenOdd

-- Mutual structural recursion over a non-mutual inductive type

-- (The functions don't actually implement even/odd, but that isn't the point here.)

mutual
  def Even : Nat → Prop
    | 0 => True
    | n+1 => ¬ Odd n
  termination_by structural x => x

  def Odd : Nat → Prop
    | 0 => False
    | n+1 => ¬ Even n
end

mutual
  def isEven : Nat → Bool
    | 0 => true
    | n+1 => ! isOdd n
  termination_by structural x => x

  def isOdd : Nat → Bool
    | 0 => false
    | n+1 => ! isEven n
end

theorem isEven_eq_2 (n : Nat) : isEven (n+1) = ! isOdd n := rfl

/-- info: EvenOdd.isEven.eq_1 : isEven 0 = true -/
#guard_msgs in
#check isEven.eq_1

theorem eq_true_of_not_eq_false {b : Bool} : (! b) = false → b = true := by simp
theorem eq_false_of_not_eq_true {b : Bool} : (! b) = true → b = false := by simp

/--
info: n : Nat
h : isOdd (n + 1) = false
⊢ isEven n = true
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

def B.self_size : B → Nat
  | .self b => b.self_size + 1
  | .other _ => 0
  | .empty => 0
termination_by structural x => x

def A.self_size_with_param : Nat → A → Nat
  | n, .self a => a.self_size_with_param n + n
  | _, .other _ => 0
  | _, .empty => 0
termination_by structural _ x => x

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
def A.weird_size3 : A → Nat
  | .self a => a.weird_size1 + 1
  | .other _ => 0
  | .empty => 0
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

namespace DifferentTypes

-- Check error message when argument types are not mutually recursive

inductive A
  | self : A → A
  | empty

/--
error: failed to infer structural recursion:
Skipping arguments of type A, as DifferentTypes.Nat.foo has no compatible argument.
Skipping arguments of type Nat, as DifferentTypes.A.with_nat has no compatible argument.
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

set_option linter.constructorNameAsVariable false in
mutual
def A.size (n : Nat) (m : Nat) : A n → Nat
  | .a => 0
  | .b b => 1 + B.size m n b
termination_by structural t => t

def B.size (n : Nat) (m : Nat) : B m → Nat
  | .a a => 1 + A.size m n a
end

end Mutual3

/--
error: cannot use specified measure for structural recursion:
  its type FixedIndex.T is an inductive family and indices are not variables
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
error: failed to infer structural recursion:
Cannot use parameter #2:
  its type is an inductive datatype and the datatype parameter
    n
  which cannot be fixed as it is an index or depends on an index, and indices cannot be fixed parameters when using structural recursion.
-/
#guard_msgs in
def T.a {n : Nat} : T n n → Nat
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
error: failed to infer structural recursion:
Skipping arguments of type T 23, as DifferentParameters.T.b has no compatible argument.
Skipping arguments of type T 42, as DifferentParameters.T.a has no compatible argument.
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
end

end DifferentParameters

namespace ManyCombinations
-- A datatype with no size function, to avoid well-founded recursion

inductive Nattish
  | zero
  | cons : (Nat → Nattish) → Nattish

/--
error: fail to show termination for
  ManyCombinations.f
  ManyCombinations.g
with errors
failed to infer structural recursion:
Too many possible combinations of parameters of type Nattish (or please indicate the recursive argument explicitly using `termination_by structural`).


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
Call from ManyCombinations.f to ManyCombinations.g at 543:15-29:
   #1 #2 #3 #4
#5  ?  ?  ?  ?
#6  ?  ?  =  ?
#7  ?  ?  ?  =
#8  ?  =  ?  ?
Call from ManyCombinations.g to ManyCombinations.f at 546:15-29:
   #5 #6 #7 #8
#1  _  _  _  _
#2  _  _  _  ?
#3  _  ?  _  _
#4  _  _  ?  _


#1: sizeOf a
#2: sizeOf b
#3: sizeOf c
#4: sizeOf d
#5: sizeOf a
#6: sizeOf b
#7: sizeOf c
#8: sizeOf d

Please use `termination_by` to specify a decreasing measure.
-/
#guard_msgs in
mutual
def f (a b c d : Nattish) : Nat := match a with
  | .zero => 0
  | .cons n => g (n 23) c d b
def g (a b c d : Nattish) : Nat := match a with
  | .zero => 0
  | .cons n => f (n 42) b c d
end

-- specifying one `termination_by structural` helps

#guard_msgs in
mutual
def f' (a b c d : Nattish) : Nat := match a with
  | .zero => 0
  | .cons n => g' (n 23) b c d
termination_by structural a
def g' (a b c d : Nattish) : Nat := match a with
  | .zero => 0
  | .cons n => f' (n 42) b c d
end

end ManyCombinations

namespace WithTuple

inductive Tree (α : Type) where
  | node : α → (Tree α × Tree α) → Tree α

mutual

def Tree.map (f : α → β) (x : Tree α): Tree β :=
  match x with
    | node x arrs => node (f x) $ Tree.map_tup f arrs
termination_by structural x

def Tree.map_tup (f : α → β) (x : Tree α × Tree α): (Tree β × Tree β) :=
  match x with
    | (t₁,t₂) => (Tree.map f t₁, Tree.map f t₂)
termination_by structural x

end

end WithTuple

namespace WithArray

inductive Tree (α : Type) where
  | node : α → Array (Tree α) → Tree α

mutual

def Tree.map (f : α → β) (x : Tree α): Tree β :=
  match x with
    | node x arr₁ => node (f x) $ Tree.map_arr f arr₁
termination_by structural x

def Tree.map_arr (f : α → β) (x : Array (Tree α)): Array (Tree β) :=
  match x with
    | .mk arr₁ => .mk (Tree.map_list f arr₁)
termination_by structural x

def Tree.map_list (f : α → β) (x : List (Tree α)): List (Tree β) :=
  match x with
    | [] => []
    | h₁::t₁ => (Tree.map f h₁)::Tree.map_list f t₁
termination_by structural x
end

end WithArray

namespace FunIndTests

-- FunInd does not handle mutual structural recursion yet, so make sure we error
-- out nicely

/--
info: A.size.induct (motive_1 : A → Prop) (motive_2 : B → Prop) (case1 : ∀ (a : A), motive_1 a → motive_1 a.self)
  (case2 : ∀ (b : B), motive_2 b → motive_1 (A.other b)) (case3 : motive_1 A.empty)
  (case4 : ∀ (b : B), motive_2 b → motive_2 b.self) (case5 : ∀ (a : A), motive_1 a → motive_2 (B.other a))
  (case6 : motive_2 B.empty) (a✝ : A) : motive_1 a✝
-/
#guard_msgs in
#check A.size.induct

/--
info: A.subs.induct (motive_1 : A → Prop) (motive_2 : B → Prop) (case1 : ∀ (a : A), motive_1 a → motive_1 a.self)
  (case2 : ∀ (b : B), motive_2 b → motive_1 (A.other b)) (case3 : motive_1 A.empty)
  (case4 : ∀ (b : B), motive_2 b → motive_2 b.self) (case5 : ∀ (a : A), motive_1 a → motive_2 (B.other a))
  (case6 : motive_2 B.empty) (a : A) : motive_1 a
-/
#guard_msgs in
#check A.subs.induct

/--
info: MutualIndNonMutualFun.A.self_size.induct (motive : MutualIndNonMutualFun.A → Prop)
  (case1 : ∀ (a : MutualIndNonMutualFun.A), motive a → motive a.self)
  (case2 : ∀ (a : MutualIndNonMutualFun.B), motive (MutualIndNonMutualFun.A.other a))
  (case3 : motive MutualIndNonMutualFun.A.empty) (a✝ : MutualIndNonMutualFun.A) : motive a✝
-/
#guard_msgs in
#check MutualIndNonMutualFun.A.self_size.induct

/--
info: MutualIndNonMutualFun.A.self_size_with_param.induct (motive : Nat → MutualIndNonMutualFun.A → Prop)
  (case1 : ∀ (n : Nat) (a : MutualIndNonMutualFun.A), motive n a → motive n a.self)
  (case2 : ∀ (x : Nat) (a : MutualIndNonMutualFun.B), motive x (MutualIndNonMutualFun.A.other a))
  (case3 : ∀ (x : Nat), motive x MutualIndNonMutualFun.A.empty) (a✝ : Nat) (a✝¹ : MutualIndNonMutualFun.A) :
  motive a✝ a✝¹
-/
#guard_msgs in
#check MutualIndNonMutualFun.A.self_size_with_param.induct

/--
info: A.hasNoBEmpty.induct (motive_1 : A → Prop) (motive_2 : B → Prop) (case1 : ∀ (a : A), motive_1 a → motive_1 a.self)
  (case2 : ∀ (b : B), motive_2 b → motive_1 (A.other b)) (case3 : motive_1 A.empty)
  (case4 : ∀ (b : B), motive_2 b → motive_2 b.self) (case5 : ∀ (a : A), motive_1 a → motive_2 (B.other a))
  (case6 : motive_2 B.empty) (a✝ : A) : motive_1 a✝
-/
#guard_msgs in
#check A.hasNoBEmpty.induct

/--
info: EvenOdd.isEven.induct (motive_1 motive_2 : Nat → Prop) (case1 : motive_1 0)
  (case2 : ∀ (n : Nat), motive_2 n → motive_1 n.succ) (case3 : motive_2 0)
  (case4 : ∀ (n : Nat), motive_1 n → motive_2 n.succ) (a✝ : Nat) : motive_1 a✝
-/
#guard_msgs in
#check EvenOdd.isEven.induct

/--
info: WithTuple.Tree.map.induct {α : Type} (motive_1 : WithTuple.Tree α → Prop)
  (motive_2 : WithTuple.Tree α × WithTuple.Tree α → Prop)
  (case1 :
    ∀ (x : α) (arrs : WithTuple.Tree α × WithTuple.Tree α), motive_2 arrs → motive_1 (WithTuple.Tree.node x arrs))
  (case2 : ∀ (t₁ t₂ : WithTuple.Tree α), motive_1 t₁ → motive_1 t₂ → motive_2 (t₁, t₂)) (x : WithTuple.Tree α) :
  motive_1 x
-/
#guard_msgs in
#check WithTuple.Tree.map.induct

/--
info: WithArray.Tree.map.induct {α : Type} (motive_1 : WithArray.Tree α → Prop) (motive_2 : Array (WithArray.Tree α) → Prop)
  (motive_3 : List (WithArray.Tree α) → Prop)
  (case1 : ∀ (x : α) (arr₁ : Array (WithArray.Tree α)), motive_2 arr₁ → motive_1 (WithArray.Tree.node x arr₁))
  (case2 : ∀ (arr₁ : List (WithArray.Tree α)), motive_3 arr₁ → motive_2 { toList := arr₁ }) (case3 : motive_3 [])
  (case4 : ∀ (h₁ : WithArray.Tree α) (t₁ : List (WithArray.Tree α)), motive_1 h₁ → motive_3 t₁ → motive_3 (h₁ :: t₁))
  (x : WithArray.Tree α) : motive_1 x
-/
#guard_msgs in
#check WithArray.Tree.map.induct

end FunIndTests
