structure Foo where
  name  : String
  val   : List Nat
  lower : Nat := List.length val
  inv   : val.length >= lower
  flag  : Bool
  deriving Hashable

#eval hash <| { name := "Joe", val := List.iota 40, flag := true, inv := by decide : Foo }

inductive Tree (α : Type) where
  | node : List (Tree α) → Bool → Tree α
  | leaf : α → Tree α
  deriving Hashable

#eval hash <| Tree.node (List.iota 10 |>.map fun i => Tree.node [Tree.leaf i] (i%2==0)) true

inductive StructureLikeInductive where
  | field : Nat -> StructureLikeInductive
  deriving Hashable

#eval StructureLikeInductive.field 5 |> hash

namespace Foo
mutual
inductive Tree (α : Type u) where
  | node : TreeList α → Tree α
  | leaf : α → Tree α
  deriving Hashable

inductive TreeList (α : Type u) where
  | nil : TreeList α
  | cons : Tree α → TreeList α → TreeList α
  deriving Hashable
end

#eval hash <| Tree.node (TreeList.cons (Tree.leaf 30) (TreeList.cons (Tree.leaf 20) (TreeList.cons (Tree.leaf 10) TreeList.nil)))

end Foo
