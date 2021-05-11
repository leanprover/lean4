universe u v

inductive myList (α : Type u)
| nil  : myList α
| cons : α → myList α → myList α

inductive myPair (α : Type u) (β : Type v)
| mk : α → β → myPair α β

mutual
variable (α : Type u) (m : α → Type v)
inductive bla : Nat → Type (max u v)
| mk₁ (n : Nat) : α → boo n → bla (n+1)
| mk₂ (a : α)   : m a → String → bla 0
inductive boo : Nat → Type (max u v)
| mk₃ (n : Nat) : bla n → bla (n+1) → boo (n+2)
end

#print bla

inductive Term (α : Type) (β : Type)
| var : α → bla (Term α β) (fun _ => Term α β) 10 → Term α β
| foo (p : Nat → myPair (Term α β) (myList $ Term α β)) (n : β) : myList (myList $ Term α β) → Term α β

#print Term
#print Term.below
#check @Term.casesOn
#print Term.noConfusionType
#print Term.noConfusion

inductive arrow (α β : Type)
| mk (s : Nat → myPair α β) : arrow α β

mutual
inductive tst1
| mk : (arrow (myPair tst2 Bool) tst2) → tst1
inductive tst2
| mk : tst1 → tst2
end

#check @tst1.casesOn
#check @tst2.casesOn
#check @tst1.recOn

namespace test

inductive Rbnode (α : Type u)
| leaf                                                        : Rbnode α
| redNode   (lchild : Rbnode α) (val : α) (rchild : Rbnode α) : Rbnode α
| blackNode (lchild : Rbnode α) (val : α) (rchild : Rbnode α) : Rbnode α

#reduce sizeOf <| Rbnode.redNode Rbnode.leaf 10 Rbnode.leaf

#check @Rbnode.brecOn

namespace Rbnode
variable {α : Type u}

constant insert (lt : α → α → Prop) [DecidableRel lt] (t : Rbnode α) (x : α) : Rbnode α := Rbnode.leaf

inductive WellFormed (lt : α → α → Prop) : Rbnode α → Prop
| leafWff : WellFormed lt leaf
| insertWff {n n' : Rbnode α} {x : α} (s : DecidableRel lt) : WellFormed lt n → n' = insert lt n x → WellFormed lt n'

end Rbnode

def Rbtree (α : Type u) (lt : α → α → Prop) : Type u :=
{t : Rbnode α // t.WellFormed lt }

inductive Trie
| Empty : Trie
| mk    : Char → Rbnode (myPair Char Trie) → Trie

#print Trie.rec
#print Trie.noConfusion
end test

inductive Foo
| mk : List Foo → Foo

#check Foo
