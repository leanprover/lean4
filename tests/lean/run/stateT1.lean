meta definition mytactic (A : Type) := state_t (list nat) tactic A

attribute [instance]
meta definition mytactic_is_monad : monad mytactic :=
@state_t.monad _ _ _

meta definition read_lst : mytactic (list nat) :=
state_t.read

meta definition write_lst : list nat → mytactic unit :=
state_t.write

meta definition foo : mytactic unit :=
write_lst [10, 20]

meta definition ins (a : nat) : mytactic unit :=
do l : list nat ← read_lst,
   write_lst (a :: l)

meta definition invoke (s : list nat) (m : mytactic unit) : tactic (list nat) :=
do (u, s') ← m s, return s'

meta definition tactic_to_mytactic {A : Type} (t : tactic A) : mytactic A :=
λ s, do a : A ← t, return (a, s)

open tactic

example : list nat :=
by do
   l : list nat ← invoke [] (foo >> ins 30 >> tactic_to_mytactic (trace "foo") >> ins 40),
   trace l,
   mk_const `list.nil >>= apply
