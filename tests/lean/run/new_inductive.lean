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

inductive term (α : Type) (β : Type)
| var : α → bla term (λ _, term) 10 → term
| foo (p : nat → my_pair term (my_list term)) (n : β) : my_list (my_list term) → term

#check @term.cases_on

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
