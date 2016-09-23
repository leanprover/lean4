meta_definition mytactic (A : Type) := stateT (list nat) tactic A

attribute [instance]
meta_definition mytactic_is_monad : monad mytactic :=
@stateT.monad _ _ _

meta_definition read_lst : mytactic (list nat) :=
stateT.read

meta_definition write_lst : list nat → mytactic unit :=
stateT.write

meta_definition foo : mytactic unit :=
write_lst [10, 20]

meta_definition ins (a : nat) : mytactic unit :=
do l : list nat ← read_lst,
   write_lst (a :: l)

meta_definition invoke (s : list nat) (m : mytactic unit) : tactic (list nat) :=
do (u, s') ← m s, return s'

meta_definition tactic_to_mytactic {A : Type} (t : tactic A) : mytactic A :=
λ s, do a : A ← t, return (a, s)

open tactic

example : list nat :=
by do
   l : list nat ← invoke [] (foo >> ins 30 >> tactic_to_mytactic (trace "foo") >> ins 40),
   trace l,
   mk_const `list.nil >>= apply
