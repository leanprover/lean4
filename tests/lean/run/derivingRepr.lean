structure Foo where
  name  : String
  val   : List Nat
  lower : Nat := List.length val
  inv   : val.length >= lower
  flag  : Bool
  deriving Repr

/--
info: { name := "Joe",
  val := [40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14,
          13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1],
  lower := 40,
  inv := _,
  flag := true }
-/
#guard_msgs in
#eval { name := "Joe", val := List.iota 40, flag := true, inv := by decide : Foo }

inductive Tree (α : Type) where
  | node : List (Tree α) → Bool → Tree α
  | leaf : α → Tree α
  deriving Repr

/--
info: Tree.node
  [Tree.node [Tree.leaf 10] true,
   Tree.node [Tree.leaf 9] false,
   Tree.node [Tree.leaf 8] true,
   Tree.node [Tree.leaf 7] false,
   Tree.node [Tree.leaf 6] true,
   Tree.node [Tree.leaf 5] false,
   Tree.node [Tree.leaf 4] true,
   Tree.node [Tree.leaf 3] false,
   Tree.node [Tree.leaf 2] true,
   Tree.node [Tree.leaf 1] false]
  true
-/
#guard_msgs in
#eval Tree.node (List.iota 10 |>.map fun i => Tree.node [Tree.leaf i] (i%2==0)) true

inductive StructureLikeInductive where
  | field : Nat -> StructureLikeInductive
  deriving Repr

/-- info: StructureLikeInductive.field 5 -/
#guard_msgs in
#eval StructureLikeInductive.field 5

namespace Foo
mutual
inductive Tree (α : Type u) where
  | node : TreeList α → Tree α
  | leaf : α → Tree α
  deriving Repr

inductive TreeList (α : Type u) where
  | nil : TreeList α
  | cons : Tree α → TreeList α → TreeList α
  deriving Repr
end

/--
info: Foo.Tree.node
  (Foo.TreeList.cons
    (Foo.Tree.leaf 30)
    (Foo.TreeList.cons (Foo.Tree.leaf 20) (Foo.TreeList.cons (Foo.Tree.leaf 10) (Foo.TreeList.nil))))
-/
#guard_msgs in
#eval Tree.node (TreeList.cons (Tree.leaf 30) (TreeList.cons (Tree.leaf 20) (TreeList.cons (Tree.leaf 10) TreeList.nil)))

end Foo

/-!
Check that types and proofs are erased for both `inductive` and `structure`.
-/

inductive test1 : Type 1 where
  | wrap : Type → 2 < 3 → test1
  deriving Repr

structure test2 : Type 1 where
  ty : Type
  wrap : 2 < 3
  deriving Repr

/-- info: test1.wrap _ _ -/
#guard_msgs in #eval test1.wrap Nat (by simp)
/-- info: { ty := _, wrap := _ } -/
#guard_msgs in #eval test2.mk Nat (by simp)

/-!
Indices promoted to parameters are still explicit. Need to include them as arguments.
-/

inductive Promote : (loc : Int) -> (state : Nat) -> Type where
  | mk : (loc : Int) -> (state : Nat) -> (id : Nat) -> Promote loc state
  deriving Repr

/-- info: Promote.mk 3 2 1 -/
#guard_msgs in #eval Promote.mk 3 2 1

/-!
Promoted indices that are types are represented as `_`.
-/

inductive Promote2 : Type → Type where
  | mk : (α : Type) → Promote2 α
  deriving Repr

/-- info: Promote2.mk _ -/
#guard_msgs in #eval Promote2.mk Nat
