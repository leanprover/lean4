universes u v

inductive myList (α : Type u)
| nil  : myList
| cons : α → myList → myList

inductive myPair (α : Type u) (β : Type v)
| mk : α → β → myPair

mutual inductive bla, boo (α : Type u) (m : α → Type v)
with bla : Nat → Type (max u v)
| mk₁ (n : Nat) : α → boo n → bla (n+1)
| mk₂ (a : α)   : m a → String → bla 0
with boo : Nat → Type (max u v)
| mk₃ (n : Nat) : bla n → bla (n+1) → boo (n+2)

#print bla

inductive Term (α : Type) (β : Type)
| var : α → bla Term (λ _, Term) 10 → Term
| foo (p : Nat → myPair Term (myList Term)) (n : β) : myList (myList Term) → Term

#print Term
#print Term.below
#check @Term.casesOn
#print Term.noConfusionType
#print Term.noConfusion

inductive arrow (α β : Type)
| mk (s : Nat → myPair α β) : arrow

mutual inductive tst1, tst2
with tst1 : Type
| mk : (arrow (myPair tst2 Bool) tst2) → tst1
with tst2 : Type
| mk : tst1 → tst2

#check @tst1.casesOn
#check @tst2.casesOn
#check @tst1.recOn

namespace test

inductive Rbnode (α : Type u)
| leaf  {}                                                 : Rbnode
| redNode   (lchild : Rbnode) (val : α) (rchild : Rbnode) : Rbnode
| blackNode (lchild : Rbnode) (val : α) (rchild : Rbnode) : Rbnode

#check @Rbnode.brecOn

namespace Rbnode
variables {α : Type u}

constant insert (lt : α → α → Prop) [decidableRel lt] (t : Rbnode α) (x : α) : Rbnode α

inductive WellFormed (lt : α → α → Prop) : Rbnode α → Prop
| leafWff : WellFormed leaf
| insertWff {n n' : Rbnode α} {x : α} (s : decidableRel lt) : WellFormed n → n' = insert lt n x → WellFormed n'

end Rbnode

def Rbtree (α : Type u) (lt : α → α → Prop) : Type u :=
{t : Rbnode α // t.WellFormed lt }

inductive Trie
| Empty : Trie
| mk    : Char → Rbnode (myPair Char Trie) → Trie

#print Trie.rec
#print Trie.noConfusion
end test
