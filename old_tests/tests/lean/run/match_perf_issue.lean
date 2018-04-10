def f : nat → bool
| 0 := ff
| _ := tt

inductive tree
| leaf : nat → tree
| node : nat → tree → tree → tree

def mk_tree : nat → nat → tree
| 0     v := tree.leaf v
| (n+1) v :=
  let t := mk_tree n v in
  tree.node v t t

def tst : tree → nat
| (tree.leaf v) := v
| (tree.node v l r) :=
  match f v with
  | tt := tst l
  | ff := tst r
  end

def tree.is_node : tree → bool
| (tree.leaf v) := ff
| _             := tt

#eval timeit "tst" $ tst (mk_tree 100 10)
