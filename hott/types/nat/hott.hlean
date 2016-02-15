/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about the natural numbers specific to HoTT
-/

import .order types.pointed

open is_trunc unit empty eq equiv algebra pointed

namespace nat
  definition is_prop_le [instance] (n m : ℕ) : is_prop (n ≤ m) :=
  begin
    assert lem : Π{n m : ℕ} (p : n ≤ m) (q : n = m), p = q ▸ le.refl n,
    { intros, cases p,
      { assert H' : q = idp, apply is_set.elim,
        cases H', reflexivity},
      { cases q, exfalso, apply not_succ_le_self a}},
    apply is_prop.mk, intro H1 H2, induction H2,
    { apply lem},
    { cases H1,
      { exfalso, apply not_succ_le_self a},
      { exact ap le.step !v_0}},
  end

  definition is_prop_lt [instance] (n m : ℕ) : is_prop (n < m) := !is_prop_le

  definition le_equiv_succ_le_succ (n m : ℕ) : (n ≤ m) ≃ (succ n ≤ succ m) :=
  equiv_of_is_prop succ_le_succ le_of_succ_le_succ
  definition le_succ_equiv_pred_le (n m : ℕ) : (n ≤ succ m) ≃ (pred n ≤ m) :=
  equiv_of_is_prop pred_le_pred le_succ_of_pred_le

  theorem lt_by_cases_lt {a b : ℕ} {P : Type} (H1 : a < b → P) (H2 : a = b → P)
    (H3 : a > b → P) (H : a < b) : lt.by_cases H1 H2 H3 = H1 H :=
  begin
    unfold lt.by_cases, induction (lt.trichotomy a b) with H' H',
     { esimp, exact ap H1 !is_prop.elim},
     { exfalso, cases H' with H' H', apply lt.irrefl, exact H' ▸ H, exact lt.asymm H H'}
  end

  theorem lt_by_cases_eq {a b : ℕ} {P : Type} (H1 : a < b → P) (H2 : a = b → P)
    (H3 : a > b → P) (H : a = b) : lt.by_cases H1 H2 H3 = H2 H :=
  begin
    unfold lt.by_cases, induction (lt.trichotomy a b) with H' H',
    { exfalso, apply lt.irrefl, exact H ▸ H'},
    { cases H' with H' H', esimp, exact ap H2 !is_prop.elim, exfalso, apply lt.irrefl, exact H ▸ H'}
  end

  theorem lt_by_cases_ge {a b : ℕ} {P : Type} (H1 : a < b → P) (H2 : a = b → P)
    (H3 : a > b → P) (H : a > b) : lt.by_cases H1 H2 H3 = H3 H :=
  begin
    unfold lt.by_cases, induction (lt.trichotomy a b) with H' H',
    { exfalso, exact lt.asymm H H'},
    { cases H' with H' H', exfalso, apply lt.irrefl, exact H' ▸ H, esimp, exact ap H3 !is_prop.elim}
  end

  theorem lt_ge_by_cases_lt {n m : ℕ} {P : Type} (H1 : n < m → P) (H2 : n ≥ m → P)
    (H : n < m) : lt_ge_by_cases H1 H2 = H1 H :=
  by apply lt_by_cases_lt

  theorem lt_ge_by_cases_ge {n m : ℕ} {P : Type} (H1 : n < m → P) (H2 : n ≥ m → P)
    (H : n ≥ m) : lt_ge_by_cases H1 H2 = H2 H :=
  begin
    unfold [lt_ge_by_cases,lt.by_cases], induction (lt.trichotomy n m) with H' H',
    { exfalso, apply lt.irrefl, exact lt_of_le_of_lt H H'},
    { cases H' with H' H'; all_goals (esimp; apply ap H2 !is_prop.elim)}
  end

  theorem lt_ge_by_cases_le {n m : ℕ} {P : Type} {H1 : n ≤ m → P} {H2 : n ≥ m → P}
    (H : n ≤ m) (Heq : Π(p : n = m), H1 (le_of_eq p) = H2 (le_of_eq p⁻¹))
    : lt_ge_by_cases (λH', H1 (le_of_lt H')) H2 = H1 H :=
  begin
    unfold [lt_ge_by_cases,lt.by_cases], induction (lt.trichotomy n m) with H' H',
    { esimp, apply ap H1 !is_prop.elim},
    { cases H' with H' H',
      { esimp, induction H', esimp, symmetry,
        exact ap H1 !is_prop.elim ⬝ Heq idp ⬝ ap H2 !is_prop.elim},
      { exfalso, apply lt.irrefl, apply lt_of_le_of_lt H H'}}
  end

  protected definition code [reducible] [unfold 1 2] : ℕ → ℕ → Type₀
  | code 0        0        := unit
  | code 0        (succ m) := empty
  | code (succ n) 0        := empty
  | code (succ n) (succ m) := code n m

  protected definition refl : Πn, nat.code n n
  | refl 0        := star
  | refl (succ n) := refl n

  protected definition encode [unfold 3] {n m : ℕ} (p : n = m) : nat.code n m :=
  p ▸ nat.refl n

  protected definition decode : Π(n m : ℕ), nat.code n m → n = m
  | decode 0        0        := λc, idp
  | decode 0        (succ l) := λc, empty.elim c _
  | decode (succ k) 0        := λc, empty.elim c _
  | decode (succ k) (succ l) := λc, ap succ (decode k l c)

  definition nat_eq_equiv (n m : ℕ) : (n = m) ≃ nat.code n m :=
  equiv.MK nat.encode
           !nat.decode
           begin
             revert m, induction n, all_goals (intro m;induction m;all_goals intro c),
               all_goals try contradiction,
               induction c, reflexivity,
               xrewrite [↑nat.decode,-tr_compose,v_0],
           end
           begin
             intro p, induction p, esimp, induction n,
               reflexivity,
               rewrite [↑nat.decode,↑nat.refl,v_0]
           end

  definition pointed_nat [instance] [constructor] : pointed ℕ :=
  pointed.mk 0

end nat
