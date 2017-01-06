inductive vec (A : Type*) : nat -> Type*
| vnil : vec 0
| vcons : Pi (n : nat), A -> vec n -> vec (n+1)

inductive tree (A : Type*)
| leaf : A -> tree
| node : Pi (n : nat), vec (list (list tree)) n -> tree

-- set_option trace.eqn_compiler true

constant P {A : Type*} : tree A → Type
constant mk1 {A : Type*} (a : A) : P (tree.leaf a)
constant mk2 {A : Type*} (n : nat) (xs : vec (list (list (tree A))) n) : P (tree.node n xs)

noncomputable definition bla {A : Type*} : ∀ n : tree A, P n
| (tree.leaf a) := mk1 a
| (tree.node n xs) := mk2 n xs

check bla._main.equations._eqn_1
check bla._main.equations._eqn_2

noncomputable definition foo {A : Type*} : nat → tree A → nat
| 0     _                                     := sorry
| (n+1) (tree.leaf a)                         := 0
| (n+1) (tree.node m xs)                      := foo n (tree.node m xs)

check @foo._main.equations._eqn_1
check @foo._main.equations._eqn_2
check @foo._main.equations._eqn_3
