import hit.quotient

open quotient eq sum

  constants {A : Type} (R : A → A → Type)

  local abbreviation C := quotient R

  definition f [unfold 2] (a : A) (x : unit) : C :=
  !class_of a

  inductive S : C → C → Type :=
  | Rmk {} : Π(a : A) (x : unit), S (f a x) (!class_of a)

  set_option pp.notation false
  set_option pp.beta false

  definition rec {P : quotient S → Type} (x : quotient S) : P x :=
  begin
    induction x with c c c' H,
    { induction c with b b b' H,
      { apply sorry},
      { apply sorry}},
    { cases H, esimp, induction x,
      { state, esimp, state, esimp, state, apply sorry}},
  end
