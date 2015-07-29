import types.eq types.pi hit.colimit

open eq is_trunc unit quotient seq_colim equiv

namespace one_step_tr
section
  parameters {A : Type}
  variables (a a' : A)

  protected definition R (a a' : A) : Type₀ := unit
  parameter (A)
  definition one_step_tr : Type := quotient R
  parameter {A}
  definition tr : one_step_tr :=
  class_of R a

  definition tr_eq : tr a = tr a' :=
  eq_of_rel _ star

  protected definition rec {P : one_step_tr → Type} (Pt : Π(a : A), P (tr a))
    (Pe : Π(a a' : A), Pt a =[tr_eq a a'] Pt a') (x : one_step_tr) : P x :=
  begin
    fapply (quotient.rec_on x),
    { intro a, apply Pt},
    { intro a a' H, cases H, apply Pe}
  end

  protected definition elim {P : Type} (Pt : A → P)
    (Pe : Π(a a' : A), Pt a = Pt a') (x : one_step_tr) : P :=
  rec Pt (λa a', pathover_of_eq (Pe a a')) x

  theorem rec_tr_eq {P : one_step_tr → Type} (Pt : Π(a : A), P (tr a))
    (Pe : Π(a a' : A), Pt a =[tr_eq a a'] Pt a') (a a' : A)
    : apdo (rec Pt Pe) (tr_eq a a') = Pe a a' :=
  !rec_eq_of_rel

  theorem elim_tr_eq {P : Type} (Pt : A → P)
    (Pe : Π(a a' : A), Pt a = Pt a') (a a' : A)
    : ap (elim Pt Pe) (tr_eq a a') = Pe a a' :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (tr_eq a a')),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑elim,rec_tr_eq],
  end

end

end one_step_tr
attribute one_step_tr.rec one_step_tr.elim [recursor 5]
open one_step_tr

definition one_step_tr_up (A B : Type)
  : (one_step_tr A → B) ≃ Σ(f : A → B), Π(x y : A), f x = f y :=
begin
  fapply equiv.MK,
  { intro f, fconstructor, intro a, exact f (tr a), intros, exact ap f !tr_eq},
  { exact sorry},
  { exact sorry},
  { exact sorry},
end
