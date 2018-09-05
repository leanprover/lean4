set_option new_inductive true
universes u v

inductive my_list (α : Type u)
| nil  : my_list
| cons : α → my_list → my_list

inductive my_pair (α : Type u) (β : Type v)
| mk : α → β → my_pair

mutual inductive bla, boo (α : Type u) (m : α → Type v)
with bla : nat → Type (max u v)
| mk₁ (n : nat) : α → boo n → bla (n+1)
| mk₂ (a : α)   : m a → string → bla 0
with boo : nat → Type (max u v)
| mk₃ (n : nat) : bla n → bla (n+1) → boo (n+2)

#print bla

inductive term (α : Type) (β : Type)
| var : α → bla term (λ _, term) 10 → term
| foo (p : nat → my_pair term (my_list term)) (n : β) : my_list (my_list term) → term

#print term
#print term.below
#check @term.cases_on
#print term.no_confusion_type
#print term.no_confusion

inductive arrow (α β : Type)
| mk (s : nat → my_pair α β) : arrow

mutual inductive tst1, tst2
with tst1 : Type
| mk : (arrow (my_pair tst2 bool) tst2) → tst1
with tst2 : Type
| mk : tst1 → tst2

#check @tst1.cases_on
#check @tst2.cases_on
#check @tst1.rec_on

namespace test

inductive rbnode (α : Type u)
| leaf  {}                                                 : rbnode
| red_node   (lchild : rbnode) (val : α) (rchild : rbnode) : rbnode
| black_node (lchild : rbnode) (val : α) (rchild : rbnode) : rbnode

namespace rbnode
variables {α : Type u}

constant insert (lt : α → α → Prop) [decidable_rel lt] (t : rbnode α) (x : α) : rbnode α

inductive well_formed (lt : α → α → Prop) : rbnode α → Prop
| leaf_wff : well_formed leaf
| insert_wff {n n' : rbnode α} {x : α} (s : decidable_rel lt) : well_formed n → n' = insert lt n x → well_formed n'

end rbnode

def rbtree (α : Type u) (lt : α → α → Prop) : Type u :=
{t : rbnode α // t.well_formed lt }

inductive trie
| empty : trie
| mk    : char → rbnode (my_pair char trie) → trie

#print trie.rec
#print trie.no_confusion
end test
