/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about the natural numbers specific to HoTT
-/

import .basic

open is_trunc unit empty eq equiv

namespace nat
  definition is_hprop_le [instance] (n m : ℕ) : is_hprop (n ≤ m) :=
  begin
    assert lem : Π{n m : ℕ} (p : n ≤ m) (q : n = m), p = q ▸ le.refl n,
    { intros, cases p,
      { assert H' : q = idp, apply is_hset.elim,
        cases H', reflexivity},
      { cases q, exfalso, apply not_succ_le_self a}},
    apply is_hprop.mk, intro H1 H2, induction H2,
    { apply lem},
    { cases H1,
      { exfalso, apply not_succ_le_self a},
      { exact ap le.step !v_0}},
  end

  definition le_equiv_succ_le_succ (n m : ℕ) : (n ≤ m) ≃ (succ n ≤ succ m) :=
  equiv_of_is_hprop succ_le_succ le_of_succ_le_succ
  definition le_succ_equiv_pred_le (n m : ℕ) : (n ≤ succ m) ≃ (pred n ≤ m) :=
  equiv_of_is_hprop pred_le_pred le_succ_of_pred_le

  theorem lt_by_cases_lt {a b : ℕ} {P : Type} (H1 : a < b → P) (H2 : a = b → P)
    (H3 : a > b → P) (H : a < b) : lt.by_cases H1 H2 H3 = H1 H :=
  begin
    unfold lt.by_cases, generalize (lt.trichotomy a b), intro X, induction X with H' H',
    { esimp, exact ap H1 !is_hprop.elim},
    { exfalso, cases H' with H' H', apply lt.irrefl, exact H' ▸ H, exact lt.asymm H H'}
  end

  theorem lt_by_cases_eq {a b : ℕ} {P : Type} (H1 : a < b → P) (H2 : a = b → P)
    (H3 : a > b → P) (H : a = b) : lt.by_cases H1 H2 H3 = H2 H :=
  begin
    unfold lt.by_cases, generalize (lt.trichotomy a b), intro X, induction X with H' H',
    { exfalso, apply lt.irrefl, exact H ▸ H'},
    { cases H' with H' H', esimp, exact ap H2 !is_hprop.elim, exfalso, apply lt.irrefl, exact H ▸ H'}
  end

  theorem lt_by_cases_ge {a b : ℕ} {P : Type} (H1 : a < b → P) (H2 : a = b → P)
    (H3 : a > b → P) (H : a > b) : lt.by_cases H1 H2 H3 = H3 H :=
  begin
    unfold lt.by_cases, generalize (lt.trichotomy a b), intro X, induction X with H' H',
    { exfalso, exact lt.asymm H H'},
    { cases H' with H' H', exfalso, apply lt.irrefl, exact H' ▸ H, esimp, exact ap H3 !is_hprop.elim}
  end

  theorem lt_ge_by_cases_lt {n m : ℕ} {P : Type} (H1 : n < m → P) (H2 : n ≥ m → P)
    (H : n < m) : lt_ge_by_cases H1 H2 = H1 H :=
  by apply lt_by_cases_lt

  theorem lt_ge_by_cases_ge {n m : ℕ} {P : Type} (H1 : n < m → P) (H2 : n ≥ m → P)
    (H : n ≥ m) : lt_ge_by_cases H1 H2 = H2 H :=
  begin
    unfold [lt_ge_by_cases,lt.by_cases], generalize (lt.trichotomy n m),
    intro X, induction X with H' H',
    { exfalso, apply lt.irrefl, exact lt_of_le_of_lt H H'},
    { cases H' with H' H'; all_goals (esimp; apply ap H2 !is_hprop.elim)}
  end

  theorem lt_ge_by_cases_le {n m : ℕ} {P : Type} {H1 : n ≤ m → P} {H2 : n ≥ m → P}
    (H : n ≤ m) (Heq : Π(p : n = m), H1 (le_of_eq p) = H2 (le_of_eq p⁻¹))
    : lt_ge_by_cases (λH', H1 (le_of_lt H')) H2 = H1 H :=
  begin
    unfold [lt_ge_by_cases,lt.by_cases], generalize (lt.trichotomy n m),
    intro X, induction X with H' H',
    { esimp, apply ap H1 !is_hprop.elim},
    { cases H' with H' H',
        esimp, exact !Heq⁻¹ ⬝ ap H1 !is_hprop.elim,
        exfalso, apply lt.irrefl, apply lt_of_le_of_lt H H'}
  end

end nat
