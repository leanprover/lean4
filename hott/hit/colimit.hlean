/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Definition of general colimits and sequential colimits.
-/

/- definition of a general colimit -/
open eq nat quotient sigma equiv equiv.ops

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
  quotient colim_rel

  definition incl : colimit :=
  class_of R ⟨i, a⟩
  abbreviation ι := @incl

  definition cglue : ι (f j b) = ι b :=
  eq_of_rel colim_rel (Rmk f b)

   protected definition rec {P : colimit → Type}
    (Pincl : Π⦃i : I⦄ (x : A i), P (ι x))
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) =[cglue j x] Pincl x)
      (y : colimit) : P y :=
  begin
    fapply (quotient.rec_on y),
    { intro a, cases a, apply Pincl},
    { intro a a' H, cases H, apply Pglue}
  end

  protected definition rec_on [reducible] {P : colimit → Type} (y : colimit)
    (Pincl : Π⦃i : I⦄ (x : A i), P (ι x))
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) =[cglue j x] Pincl x) : P y :=
  rec Pincl Pglue y

  theorem rec_cglue {P : colimit → Type}
    (Pincl : Π⦃i : I⦄ (x : A i), P (ι x))
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) =[cglue j x] Pincl x)
      {j : J} (x : A (dom j)) : apdo (rec Pincl Pglue) (cglue j x) = Pglue j x :=
  !rec_eq_of_rel

  protected definition elim {P : Type} (Pincl : Π⦃i : I⦄ (x : A i), P)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) = Pincl x) (y : colimit) : P :=
  rec Pincl (λj a, pathover_of_eq (Pglue j a)) y

  protected definition elim_on [reducible] {P : Type} (y : colimit)
    (Pincl : Π⦃i : I⦄ (x : A i), P)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) = Pincl x) : P :=
  elim Pincl Pglue y

  theorem elim_cglue {P : Type}
    (Pincl : Π⦃i : I⦄ (x : A i), P)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) = Pincl x)
      {j : J} (x : A (dom j)) : ap (elim Pincl Pglue) (cglue j x) = Pglue j x :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (cglue j x)),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑elim,rec_cglue],
  end

  protected definition elim_type (Pincl : Π⦃i : I⦄ (x : A i), Type)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) ≃ Pincl x) (y : colimit) : Type :=
  elim Pincl (λj a, ua (Pglue j a)) y

  protected definition elim_type_on [reducible] (y : colimit)
    (Pincl : Π⦃i : I⦄ (x : A i), Type)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) ≃ Pincl x) : Type :=
  elim_type Pincl Pglue y

  theorem elim_type_cglue (Pincl : Π⦃i : I⦄ (x : A i), Type)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) ≃ Pincl x)
      {j : J} (x : A (dom j)) : transport (elim_type Pincl Pglue) (cglue j x) = Pglue j x :=
  by rewrite [tr_eq_cast_ap_fn,↑elim_type,elim_cglue];apply cast_ua_fn

end
end colimit

/- definition of a sequential colimit -/
namespace seq_colim
section
  /-
    we define it directly in terms of quotients. An alternative definition could be
    definition seq_colim := colimit.colimit A function.id succ f
  -/
  parameters {A : ℕ → Type} (f : Π⦃n⦄, A n → A (succ n))
  variables {n : ℕ} (a : A n)

  local abbreviation B := Σ(n : ℕ), A n
  inductive seq_rel : B → B → Type :=
  | Rmk : Π{n : ℕ} (a : A n), seq_rel ⟨succ n, f a⟩ ⟨n, a⟩
  open seq_rel
  local abbreviation R := seq_rel

  -- TODO: define this in root namespace
  definition seq_colim : Type :=
  quotient seq_rel

  definition inclusion : seq_colim :=
  class_of R ⟨n, a⟩

  abbreviation sι := @inclusion

  definition glue : sι (f a) = sι a :=
  eq_of_rel seq_rel (Rmk f a)

  protected definition rec {P : seq_colim → Type}
    (Pincl : Π⦃n : ℕ⦄ (a : A n), P (sι a))
    (Pglue : Π(n : ℕ) (a : A n), Pincl (f a) =[glue a] Pincl a) (aa : seq_colim) : P aa :=
  begin
    fapply (quotient.rec_on aa),
    { intro a, cases a, apply Pincl},
    { intro a a' H, cases H, apply Pglue}
  end

  protected definition rec_on [reducible] {P : seq_colim → Type} (aa : seq_colim)
    (Pincl : Π⦃n : ℕ⦄ (a : A n), P (sι a))
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) =[glue a] Pincl a)
      : P aa :=
  rec Pincl Pglue aa

  theorem rec_glue {P : seq_colim → Type} (Pincl : Π⦃n : ℕ⦄ (a : A n), P (sι a))
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) =[glue a] Pincl a) {n : ℕ} (a : A n)
      : apdo (rec Pincl Pglue) (glue a) = Pglue a :=
  !rec_eq_of_rel

  protected definition elim {P : Type} (Pincl : Π⦃n : ℕ⦄ (a : A n), P)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) = Pincl a) : seq_colim → P :=
  rec Pincl (λn a, pathover_of_eq (Pglue a))

  protected definition elim_on [reducible] {P : Type} (aa : seq_colim)
    (Pincl : Π⦃n : ℕ⦄ (a : A n), P)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) = Pincl a) : P :=
  elim Pincl Pglue aa

  theorem elim_glue {P : Type} (Pincl : Π⦃n : ℕ⦄ (a : A n), P)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) = Pincl a) {n : ℕ} (a : A n)
      : ap (elim Pincl Pglue) (glue a) = Pglue a :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (glue a)),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑elim,rec_glue],
  end

  protected definition elim_type (Pincl : Π⦃n : ℕ⦄ (a : A n), Type)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) ≃ Pincl a) : seq_colim → Type :=
  elim Pincl (λn a, ua (Pglue a))

  protected definition elim_type_on [reducible] (aa : seq_colim)
    (Pincl : Π⦃n : ℕ⦄ (a : A n), Type)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) ≃ Pincl a) : Type :=
  elim_type Pincl Pglue aa

  theorem elim_type_glue (Pincl : Π⦃n : ℕ⦄ (a : A n), Type)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) ≃ Pincl a) {n : ℕ} (a : A n)
      : transport (elim_type Pincl Pglue) (glue a) = Pglue a :=
  by rewrite [tr_eq_cast_ap_fn,↑elim_type,elim_glue];apply cast_ua_fn

end
end seq_colim

attribute colimit.incl seq_colim.inclusion [constructor]
attribute colimit.rec colimit.elim [unfold 10] [recursor 10]
attribute colimit.elim_type [unfold 9]
attribute colimit.rec_on colimit.elim_on [unfold 8]
attribute colimit.elim_type_on [unfold 7]
attribute seq_colim.rec seq_colim.elim [unfold 6] [recursor 6]
attribute seq_colim.elim_type [unfold 5]
attribute seq_colim.rec_on seq_colim.elim_on [unfold 4]
attribute seq_colim.elim_type_on [unfold 3]
