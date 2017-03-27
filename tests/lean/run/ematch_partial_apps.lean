open tactic

set_option trace.smt.ematch true

example (a : list nat) (f : nat → nat) : a = [1, 2] → a^.for f = [f 1, f 2] :=
begin [smt]
  intros,
  ematch_using [list.for],
  ematch_using [flip],
  ematch_using [list.map],
  ematch_using [list.map],
  ematch_using [list.map]
end

example (a : list nat) (f : nat → nat) : a = [1, 2] → a^.for f = [f 1, f 2] :=
begin [smt]
  intros,
  repeat {ematch_using [list.for, flip, list.map], try { close }},
end

attribute [ematch] list.map flip list.for

example (a : list nat) (f : nat → nat) : a = [1, 2] → a^.for f = [f 1, f 2] :=
begin [smt]
  intros, eblast
end

constant f : nat → nat → nat
constant g : nat → nat → nat
axiom fgx : ∀ x y, (: f x :) = (λ y, y) ∧ (: g y :) = λ x, 0
attribute [ematch] fgx

example (a b c : nat) : f a b = b ∧ g b c = 0 :=
begin [smt]
  ematch
end
