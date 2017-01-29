inductive {u} vec (A : Type u) : nat -> Type u
| vnil : vec 0
| vcons : Pi (n : nat), A -> vec n -> vec (n+1)

inductive {u} tree (A : Type u) : Type u
| leaf : A -> tree
| node : Pi (n : nat), vec (list (list tree)) n -> tree

-- set_option trace.eqn_compiler true

constant {u} P {A : Type u} : tree A → Type
constant {u} mk1 {A : Type u} (a : A) : P (tree.leaf a)
constant {u} mk2 {A : Type u} (n : nat) (xs : vec (list (list (tree A))) n) : P (tree.node n xs)

noncomputable definition {u} bla {A : Type u} : ∀ n : tree A, P n
| (tree.leaf a) := mk1 a
| (tree.node n xs) := mk2 n xs

check bla._main.equations._eqn_1
check bla._main.equations._eqn_2

noncomputable definition {u} foo {A : Type u} : nat → tree A → nat
| 0     _                                     := sorry
| (n+1) (tree.leaf a)                         := 0
| (n+1) (tree.node m xs)                      := foo n (tree.node m xs)

check @foo._main.equations._eqn_1
check @foo._main.equations._eqn_2
check @foo._main.equations._eqn_3
