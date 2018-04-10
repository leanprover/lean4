constant f : nat → nat
constant p : nat → Prop
/- The following axiom produces a matching loop -/
axiom fax : ∀ x, f (: f x :) = nat.succ x
axiom px : ∀ x, p x

attribute [ematch] fax

set_option trace.smt.ematch true

lemma ex1 (a b c : nat) : f a = b → p a :=
begin [smt]
  intros, iterate {ematch},
  ematch_using [px]
end

constant r : nat → nat → Prop
axiom rtrans : ∀ a b c, r a b → r b c → r a c
attribute [ematch] rtrans

example (a1 a2 a3 a4 a5 a6 a7 a8 : nat) :
  r a1 a2 → r a2 a3 → r a3 a4 → r a4 a5 → r a5 a6 → r a6 a7 → r a7 a8 → r a1 a8 ∨ p 0 :=
begin [smt] with {em_cfg := {max_generation := 2}},
  intros,
  eblast, -- fails to prove because max_generation is too low
  ematch_using [px]
end

example (a1 a2 a3 a4 a5 a6 a7 a8 : nat) :
  r a1 a2 → r a2 a3 → r a3 a4 → r a4 a5 → r a5 a6 → r a6 a7 → r a7 a8 → r a1 a8 :=
begin [smt] with {em_cfg := {max_generation := 10}},
  intros,
  eblast -- succeeds
end

attribute [ematch] list.map

example (f : nat → nat) (l : list nat) : l = [1, 2, 3, 4, 5, 6, 7, 8, 9] → list.map f l = [f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9] ∨ p 0 :=
begin [smt] with {em_cfg := {max_generation := 5}},
  intros,
  eblast, -- fails to prove because max_generation is too low
  ematch_using [px]
end

example (f : nat → nat) (l : list nat) : l = [1, 2, 3, 4, 5, 6, 7, 8, 9] → list.map f l = [f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9] :=
begin [smt] with {em_cfg := {max_generation := 10}},
  intros,
  eblast -- succeeds
end
