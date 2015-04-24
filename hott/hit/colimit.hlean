/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: hit.colimit
Authors: Floris van Doorn

Definition of general colimits and sequential colimits.
-/

/- definition of a general colimit -/
open eq nat type_quotient sigma equiv

namespace colimit
section
  parameters {I J : Type} (A : I → Type) (dom cod : J → I)
             (f : Π(j : J), A (dom j) → A (cod j))
  variables {i : I} (a : A i) (j : J) (b : A (dom j))

  local abbreviation B := Σ(i : I), A i
  inductive colim_rel : B → B → Type :=
  | Rmk : Π{j : J} (a : A (dom j)), colim_rel ⟨cod j, f j a⟩ ⟨dom j, a⟩
  open colim_rel
  local abbreviation R := colim_rel

  -- TODO: define this in root namespace
  definition colimit : Type :=
  type_quotient colim_rel

  definition incl : colimit :=
  class_of R ⟨i, a⟩
  abbreviation ι := @incl

  definition cglue : ι (f j b) = ι b :=
  eq_of_rel (Rmk f b)

   protected definition rec {P : colimit → Type}
    (Pincl : Π⦃i : I⦄ (x : A i), P (ι x))
    (Pglue : Π(j : J) (x : A (dom j)), cglue j x ▹ Pincl (f j x) = Pincl x)
      (y : colimit) : P y :=
  begin
    fapply (type_quotient.rec_on y),
    { intro a, cases a, apply Pincl},
    { intros [a, a', H], cases H, apply Pglue}
  end

  protected definition rec_on [reducible] {P : colimit → Type} (y : colimit)
    (Pincl : Π⦃i : I⦄ (x : A i), P (ι x))
    (Pglue : Π(j : J) (x : A (dom j)), cglue j x ▹ Pincl (f j x) = Pincl x) : P y :=
  rec Pincl Pglue y

  definition rec_cglue [reducible] {P : colimit → Type}
    (Pincl : Π⦃i : I⦄ (x : A i), P (ι x))
    (Pglue : Π(j : J) (x : A (dom j)), cglue j x ▹ Pincl (f j x) = Pincl x)
      {j : J} (x : A (dom j)) : apd (rec Pincl Pglue) (cglue j x) = Pglue j x :=
  sorry

   protected definition elim {P : Type} (Pincl : Π⦃i : I⦄ (x : A i), P)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) = Pincl x) (y : colimit) : P :=
  rec Pincl (λj a, !tr_constant ⬝ Pglue j a) y

  protected definition elim_on [reducible] {P : Type} (y : colimit)
    (Pincl : Π⦃i : I⦄ (x : A i), P)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) = Pincl x) : P :=
  elim Pincl Pglue y

  definition elim_cglue [reducible] {P : Type}
    (Pincl : Π⦃i : I⦄ (x : A i), P)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) = Pincl x)
      {j : J} (x : A (dom j)) : ap (elim Pincl Pglue) (cglue j x) = Pglue j x :=
  sorry

  protected definition elim_type (Pincl : Π⦃i : I⦄ (x : A i), Type)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) ≃ Pincl x) (y : colimit) : Type :=
  elim Pincl (λj a, ua (Pglue j a)) y

  protected definition elim_type_on [reducible] (y : colimit)
    (Pincl : Π⦃i : I⦄ (x : A i), Type)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) ≃ Pincl x) : Type :=
  elim_type Pincl Pglue y

  definition elim_type_cglue [reducible] (Pincl : Π⦃i : I⦄ (x : A i), Type)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) ≃ Pincl x)
      {j : J} (x : A (dom j)) : transport (elim_type Pincl Pglue) (cglue j x) = sorry /-Pglue j x-/ :=
  sorry

end
end colimit

/- definition of a sequential colimit -/
namespace seq_colim
section
  parameters {A : ℕ → Type} (f : Π⦃n⦄, A n → A (succ n))
  variables {n : ℕ} (a : A n)

  local abbreviation B := Σ(n : ℕ), A n
  inductive seq_rel : B → B → Type :=
  | Rmk : Π{n : ℕ} (a : A n), seq_rel ⟨succ n, f a⟩ ⟨n, a⟩
  open seq_rel
  local abbreviation R := seq_rel

  -- TODO: define this in root namespace
  definition seq_colim : Type :=
  type_quotient seq_rel

  definition inclusion : seq_colim :=
  class_of R ⟨n, a⟩

  abbreviation sι := @inclusion

  definition glue : sι (f a) = sι a :=
  eq_of_rel (Rmk f a)

  protected definition rec [reducible] {P : seq_colim → Type}
    (Pincl : Π⦃n : ℕ⦄ (a : A n), P (sι a))
    (Pglue : Π(n : ℕ) (a : A n), glue a ▹ Pincl (f a) = Pincl a) (aa : seq_colim) : P aa :=
  begin
    fapply (type_quotient.rec_on aa),
    { intro a, cases a, apply Pincl},
    { intros [a, a', H], cases H, apply Pglue}
  end

  protected definition rec_on [reducible] {P : seq_colim → Type} (aa : seq_colim)
    (Pincl : Π⦃n : ℕ⦄ (a : A n), P (sι a))
    (Pglue : Π⦃n : ℕ⦄ (a : A n), glue a ▹ Pincl (f a) = Pincl a)
      : P aa :=
  rec Pincl Pglue aa

  protected definition elim {P : Type} (Pincl : Π⦃n : ℕ⦄ (a : A n), P)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) = Pincl a) : seq_colim → P :=
  rec Pincl (λn a, !tr_constant ⬝ Pglue a)

  protected definition elim_on [reducible] {P : Type} (aa : seq_colim)
    (Pincl : Π⦃n : ℕ⦄ (a : A n), P)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) = Pincl a) : P :=
  elim Pincl Pglue aa

  definition rec_glue {P : seq_colim → Type} (Pincl : Π⦃n : ℕ⦄ (a : A n), P (sι a))
    (Pglue : Π⦃n : ℕ⦄ (a : A n), glue a ▹ Pincl (f a) = Pincl a) {n : ℕ} (a : A n)
      : apd (rec Pincl Pglue) (glue a) = sorry ⬝ Pglue a ⬝ sorry :=
  sorry

  definition elim_glue {P : Type} (Pincl : Π⦃n : ℕ⦄ (a : A n), P)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) = Pincl a) {n : ℕ} (a : A n)
      : ap (elim Pincl Pglue) (glue a) = sorry ⬝ Pglue a ⬝ sorry :=
  sorry

  protected definition elim_type (Pincl : Π⦃n : ℕ⦄ (a : A n), Type)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) ≃ Pincl a) : seq_colim → Type :=
  elim Pincl (λn a, ua (Pglue a))

  protected definition elim_type_on [reducible] (aa : seq_colim)
    (Pincl : Π⦃n : ℕ⦄ (a : A n), Type)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) ≃ Pincl a) : Type :=
  elim_type Pincl Pglue aa

  definition elim_type_glue (Pincl : Π⦃n : ℕ⦄ (a : A n), Type)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) ≃ Pincl a) {n : ℕ} (a : A n)
      : transport (elim_type Pincl Pglue) (glue a) = sorry /-Pglue a-/ :=
  sorry

end
end seq_colim
