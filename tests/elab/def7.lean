inductive InfTree.{u} (α : Type u)
| leaf : α → InfTree α
| node : (Nat → InfTree α) → InfTree α

open InfTree

def szn.{u} {α : Type u} (n : Nat) : InfTree α → InfTree α → Nat
| leaf a, t2     => 1
| node c, leaf b => 0
| node c, node d => szn n (c n) (d n)

universe u

theorem ex1 {α : Type u} (n : Nat) (c : Nat → InfTree α) (d : Nat → InfTree α) : szn n (node c) (node d) = szn n (c n) (d n) :=
rfl

inductive BTree (α : Type u)
| leaf : α → BTree α
| node : (Bool → Bool → BTree α) → BTree α

def BTree.sz {α : Type u} : BTree α → Nat
| leaf a => 1
| node c => sz (c true true) + sz (c true false) + sz (c false true) + sz (c false false) + 1

theorem ex2 {α : Type u} (c : Bool → Bool → BTree α) : (BTree.node c).sz = (c true true).sz + (c true false).sz + (c false true).sz + (c false false).sz + 1 :=
rfl

inductive L (α : Type u)
| nil  : L α
| cons : (Unit → α) → (Unit → L α) → L α

def L.append {α} : L α → L α → L α
| nil, bs       => bs
| cons a as, bs => cons a (fun _ => append (as ()) bs)

theorem L.appendNil {α} : (as : L α) → append as nil = as
| nil       => rfl
| cons a as =>
  show cons a (fun _ => append (as ()) nil) = cons a as from
  have ih : append (as ()) nil = as () := appendNil $ as ()
  have thunkAux : (fun _ => as ()) = as := funext fun x => by
    cases x
    exact rfl
  by rw [ih, thunkAux]
