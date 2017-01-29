inductive {u} tree (A : Type u) : Type u
| leaf : A -> tree
| node : list tree -> tree

def foo {A : Type*} : nat → tree A → nat
| 0     _                   := 0
| (n+1) (tree.leaf a)       := 0
| (n+1) (tree.node [])      := foo n (tree.node [])
| (n+1) (tree.node (x::xs)) := foo n x
