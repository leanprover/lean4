--set_option trace.inductive_compiler.nested.define true
inductive {u} tree (A : Type u) : Type u
| leaf : A -> tree
| node : list tree -> tree

set_option trace.eqn_compiler true
definition sz {A : Type*} : tree A → nat
| (tree.leaf a) := 1
| (tree.node l) := list.length l + 1

constant P {A : Type*} : tree A → Type 1
constant mk1 {A : Type*} (a : A) : P (tree.leaf a)
constant mk2 {A : Type*} (l : list (tree A)) : P (tree.node l)

noncomputable definition bla {A : Type*} : ∀ n : tree A, P n
| (tree.leaf a) := mk1 a
| (tree.node l) := mk2 l

check bla._main.equations._eqn_1
check bla._main.equations._eqn_2

noncomputable definition foo {A : Type*} : nat → tree A → nat
| 0     _                   := sorry
| (n+1) (tree.leaf a)       := 0
| (n+1) (tree.node [])      := foo n (tree.node [])
| (n+1) (tree.node (x::xs)) := foo n x

check @foo._main.equations._eqn_1
check @foo._main.equations._eqn_2
check @foo._main.equations._eqn_3
check @foo._main.equations._eqn_4
