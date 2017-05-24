universes u v

inductive tree (α : Type u) : Type u
| node : α → list tree → tree

mutual def tree.map, tree.map_lst {α : Type u} {β : Type v} (f : α → β)
with tree.map : tree α → tree β
| (tree.node a ts) := tree.node (f a) (tree.map_lst ts)
with tree.map_lst : list (tree α) → list (tree β)
| []      := []
| (t::ts) := tree.map t :: tree.map_lst ts

example {α : Type u} {β : Type v} (f : α → β) (a : α) (ts : list (tree α)) : tree.map f (tree.node a ts) = tree.node (f a) (tree.map_lst f ts) :=
by simp [tree.map]

example {α : Type u} {β : Type v} (f : α → β) : tree.map_lst f [] = [] :=
by simp [tree.map_lst]

example {α : Type u} {β : Type v} (f : α → β) (t : tree α) (ts : list (tree α)) : tree.map_lst f (t::ts) = tree.map f t :: tree.map_lst f ts :=
by simp [tree.map_lst]
