universe u v

inductive MyList (α : Type u)
| nil  : MyList α
| cons : α → MyList α → MyList α

inductive MyPair (α : Type u) (β : Type v)
| mk : α → β → MyPair α β

mutual
variable (α : Type u) (m : α → Type v)
inductive Bla : Nat → Type (max u v)
| mk₁ (n : Nat) : α → Boo n → Bla (n+1)
| mk₂ (a : α)   : m a → String → Bla 0
inductive Boo : Nat → Type (max u v)
| mk₃ (n : Nat) : Bla n → Bla (n+1) → Boo (n+2)
end

#print Bla

inductive Term (α : Type) (β : Type)
| var : α → Bla (Term α β) (fun _ => Term α β) 10 → Term α β
| foo (p : Nat → MyPair (Term α β) (MyList $ Term α β)) (n : β) : MyList (MyList $ Term α β) → Term α β

#print Term
#print Term.below
#check @Term.casesOn
#print Term.noConfusionType
#print Term.noConfusion

inductive Arrow (α β : Type)
| mk (s : Nat → MyPair α β) : Arrow α β

mutual
inductive Tst1
| mk : (Arrow (MyPair Tst2 Bool) Tst2) → Tst1
inductive Tst2
| mk : Tst1 → Tst2
end

#check @Tst1.casesOn
#check @Tst2.casesOn
#check @Tst1.recOn

namespace Test

inductive RBNode (α : Type u)
| leaf                                                         : RBNode α
| red_node   (lchild : RBNode α) (val : α) (rchild : RBNode α) : RBNode α
| black_node (lchild : RBNode α) (val : α) (rchild : RBNode α) : RBNode α

#reduce sizeOf <| RBNode.red_node RBNode.leaf 10 RBNode.leaf

#check @RBNode.brecOn

namespace RBNode
variable {α : Type u}

opaque insert (lt : α → α → Prop) [DecidableRel lt] (t : RBNode α) (x : α) : RBNode α := RBNode.leaf

inductive WellFormed (lt : α → α → Prop) : RBNode α → Prop
| leaf_wff : WellFormed lt leaf
| insert_wff {n n' : RBNode α} {x : α} (s : DecidableRel lt) : WellFormed lt n → n' = insert lt n x → WellFormed lt n'

end RBNode

def RBTree (α : Type u) (lt : α → α → Prop) : Type u :=
{t : RBNode α // t.WellFormed lt }

inductive Trie
| empty : Trie
| mk    : Char → RBNode (MyPair Char Trie) → Trie

#print Trie.rec
#print Trie.noConfusion
end Test

inductive Foo
| mk : List Foo → Foo

#check Foo
