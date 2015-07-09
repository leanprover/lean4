/-
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Floris van Doorn

Ported from Coq HoTT
-/

import arity .eq .bool .unit .sigma
open is_trunc eq prod sigma nat equiv option is_equiv bool unit

structure pointed [class] (A : Type) :=
  (point : A)

structure Pointed :=
  {carrier : Type}
  (Point   : carrier)

open Pointed

namespace pointed
  attribute Pointed.carrier [coercion]
  variables {A B : Type}

  definition pt [unfold 2] [H : pointed A] := point A
  protected abbreviation Mk [constructor] := @Pointed.mk
  protected definition mk' [constructor] (A : Type) [H : pointed A] : Pointed :=
  Pointed.mk (point A)
  definition pointed_carrier [instance] [constructor] (A : Pointed) : pointed A :=
  pointed.mk (Point A)

  -- Any contractible type is pointed
  definition pointed_of_is_contr [instance] [priority 800] [constructor]
    (A : Type) [H : is_contr A] : pointed A :=
  pointed.mk !center

  -- A pi type with a pointed target is pointed
  definition pointed_pi [instance] [constructor] (P : A → Type) [H : Πx, pointed (P x)]
      : pointed (Πx, P x) :=
  pointed.mk (λx, pt)

  -- A sigma type of pointed components is pointed
  definition pointed_sigma [instance] [constructor] (P : A → Type) [G : pointed A]
      [H : pointed (P pt)] : pointed (Σx, P x) :=
  pointed.mk ⟨pt,pt⟩

  definition pointed_prod [instance] [constructor] (A B : Type) [H1 : pointed A] [H2 : pointed B]
      : pointed (A × B) :=
  pointed.mk (pt,pt)

  definition pointed_loop [instance] [constructor] (a : A) : pointed (a = a) :=
  pointed.mk idp

  definition pointed_bool [instance] [constructor] : pointed bool :=
  pointed.mk ff

  definition Bool [constructor] : Pointed :=
  pointed.mk' bool

  definition pointed_fun_closed [constructor] (f : A → B) [H : pointed A] : pointed B :=
  pointed.mk (f pt)

  definition Loop_space [reducible] [constructor] (A : Pointed) : Pointed :=
  pointed.mk' (point A = point A)

  -- definition Iterated_loop_space : Pointed → ℕ → Pointed
  -- | Iterated_loop_space A 0 := A
  -- | Iterated_loop_space A (n+1) := Iterated_loop_space (Loop_space A) n

  definition Iterated_loop_space [reducible] (n : ℕ) (A : Pointed) : Pointed :=
  nat.rec_on n (λA, A) (λn IH A, IH (Loop_space A)) A

  prefix `Ω`:(max+5) := Loop_space
  notation `Ω[`:95 n:0 `]`:0 A:95 := Iterated_loop_space n A

  definition iterated_loop_space (A : Type) [H : pointed A] (n : ℕ) : Type :=
  Ω[n] (pointed.mk' A)

  open equiv.ops
  definition Pointed_eq {A B : Pointed} (f : A ≃ B) (p : f pt = pt) : A = B :=
  begin
    cases A with A a, cases B with B b, esimp at *,
    fapply apd011 @Pointed.mk,
    { apply ua f},
    { rewrite [cast_ua,p]},
  end

  definition add_point [constructor] (A : Type) : Pointed :=
  Pointed.mk (none : option A)
  postfix `₊`:(max+1) := add_point
  -- the inclusion A → A₊ is called "some", the extra point "pt" or "none" ("@none A")
end pointed

open pointed
structure pmap (A B : Pointed) :=
  (map : A → B)
  (resp_pt : map (Point A) = Point B)

open pmap

namespace pointed

  abbreviation respect_pt [unfold 3] := @pmap.resp_pt
  notation `map₊` := pmap
  infix `→*`:30 := pmap
  attribute pmap.map [coercion]
  variables {A B C D : Pointed} {f g h : A →* B}

  definition pmap_eq (r : Πa, f a = g a) (s : respect_pt f = (r pt) ⬝ respect_pt g) : f = g :=
  begin
    cases f with f p, cases g with g q,
    esimp at *,
    fapply apo011 pmap.mk,
    { exact eq_of_homotopy r},
    { apply concato_eq, apply pathover_eq_Fl, apply inv_con_eq_of_eq_con,
      rewrite [ap_eq_ap10,↑ap10,apd10_eq_of_homotopy,s]}
  end

  definition pid [constructor] (A : Pointed) : A →* A :=
  pmap.mk function.id idp

  definition pcompose [constructor] (g : B →* C) (f : A →* B) : A →* C :=
  pmap.mk (λa, g (f a)) (ap g (respect_pt f) ⬝ respect_pt g)

  infixr `∘*`:60 := pcompose

  structure phomotopy (f g : A →* B) :=
    (homotopy : f ~ g)
    (homotopy_pt : homotopy pt ⬝ respect_pt g = respect_pt f)

  infix `~*`:50 := phomotopy
  abbreviation to_homotopy_pt [unfold 5] := @phomotopy.homotopy_pt
  abbreviation to_homotopy [coercion] [unfold 5] (p : f ~* g) : Πa, f a = g a :=
  phomotopy.homotopy p

  definition passoc (h : C →* D) (g : B →* C) (f : A →* B) : (h ∘* g) ∘* f ~* h ∘* (g ∘* f) :=
  begin
    fconstructor, intro a, reflexivity,
    cases A, cases B, cases C, cases D, cases f with f pf, cases g with g pg, cases h with h ph,
    esimp at *,
    induction pf, induction pg, induction ph, reflexivity
  end

  definition pid_comp (f : A →* B) : pid B ∘* f ~* f :=
  begin
    fconstructor,
    { intro a, reflexivity},
    { esimp, exact !idp_con ⬝ !ap_id⁻¹}
  end

  definition comp_pid (f : A →* B) : f ∘* pid A ~* f :=
  begin
    fconstructor,
    { intro a, reflexivity},
    { reflexivity}
  end

  definition pmap_equiv_left (A : Type) (B : Pointed) : A₊ →* B ≃ (A → B) :=
  begin
    fapply equiv.MK,
    { intro f a, cases f with f p, exact f (some a)},
    { intro f, fconstructor,
        intro a, cases a, exact pt, exact f a,
        reflexivity},
    { intro f, reflexivity},
    { intro f, cases f with f p, esimp, fapply pmap_eq,
      { intro a, cases a; all_goals (esimp at *), exact p⁻¹},
      { esimp, exact !con.left_inv⁻¹}},
  end

  -- definition Loop_space_functor (f : A →* B) : Ω A →* Ω B :=
  -- begin
  --   fapply pmap.mk,
  --   { intro p, exact ap f p},
  -- end

  -- set_option pp.notation false
  -- definition pmap_equiv_right (A : Pointed) (B : Type)
  --   : (Σ(b : B), map₊ A (pointed.Mk b)) ≃ (A → B) :=
  -- begin
  --   fapply equiv.MK,
  --   { intro u a, cases u with b f, cases f with f p, esimp at f, exact f a},
  --   { intro f, refine ⟨f pt, _⟩, fapply pmap.mk,
  --       intro a, esimp, exact f a,
  --       reflexivity},
  --   { intro f, reflexivity},
  --   { intro u, cases u with b f, cases f with f p, esimp at *, apply sigma_eq p,
  --     esimp, apply sorry
  --     }
  -- end

  definition pmap_bool_equiv (B : Pointed) : map₊ Bool B ≃ B :=
  begin
    fapply equiv.MK,
    { intro f, cases f with f p, exact f tt},
    { intro b, fconstructor,
        intro u, cases u, exact pt, exact b,
        reflexivity},
    { intro b, reflexivity},
    { intro f, cases f with f p, esimp, fapply pmap_eq,
      { intro a, cases a; all_goals (esimp at *), exact p⁻¹},
      { esimp, exact !con.left_inv⁻¹}},
  end

  definition apn [constructor] (n : ℕ) (f : map₊ A B) : Ω[n] A →* Ω[n] B :=
  begin
  revert A B f, induction n with n IH,
  { intros A B f, exact f},
  { intros A B f, esimp [Iterated_loop_space], apply IH (Ω A),
    { esimp, fconstructor,
        intro q, refine !respect_pt⁻¹ ⬝ ap f q ⬝ !respect_pt,
        esimp, apply con.left_inv}}
  end

  definition ap1 [constructor] (f : A →* B) : Ω A →* Ω B := apn (succ 0) f

  definition ap1_compose (g : B →* C) (f : A →* B) : ap1 (g ∘* f) ~* ap1 g ∘* ap1 f :=
  begin
    induction B, induction C, induction g with g pg, induction f with f pf, esimp at *,
    induction pg, induction pf,
    fconstructor,
    { intro p, esimp, apply whisker_left, exact ap_compose g f p ⬝ ap (ap g) !idp_con⁻¹},
    { reflexivity}
  end

  protected definition phomotopy.refl [refl] (f : A →* B) : f ~* f :=
  begin
    fconstructor,
    { intro a, exact idp},
    { apply idp_con}
  end

  protected definition phomotopy.trans [trans] (p : f ~* g) (q : g ~* h)
    : f ~* h :=
  begin
    fconstructor,
    { intro a, exact p a ⬝ q a},
    { induction f, induction g, induction p with p p', induction q with q q', esimp at *,
      induction p', induction q', esimp, apply con.assoc}
  end

  protected definition phomotopy.symm [symm] (p : f ~* g) : g ~* f :=
  begin
    fconstructor,
    { intro a, exact (p a)⁻¹},
    { induction f, induction p with p p', esimp at *,
      induction p', esimp, apply inv_con_cancel_left}
  end

  infix `⬝*`:75 := phomotopy.trans
  postfix `⁻¹*`:(max+1) := phomotopy.symm

  definition eq_of_phomotopy (p : f ~* g) : f = g :=
  begin
    fapply pmap_eq,
    { intro a, exact p a},
    { exact !to_homotopy_pt⁻¹}
  end

  definition pwhisker_left (h : B →* C) (p : f ~* g) : h ∘* f ~* h ∘* g :=
  begin
    fconstructor,
    { intro a, exact ap h (p a)},
    { induction A, induction B, induction C,
      induction f with f pf, induction g with g pg, induction h with h ph,
      induction p with p p', esimp at *, induction ph, induction pg, induction p', reflexivity}
  end

  definition pwhisker_right (h : C →* A) (p : f ~* g) : f ∘* h ~* g ∘* h :=
  begin
    fconstructor,
    { intro a, exact p (h a)},
    { induction A, induction B, induction C,
      induction f with f pf, induction g with g pg, induction h with h ph,
      induction p with p p', esimp at *, induction ph, induction pg, induction p', esimp,
      exact !idp_con⁻¹}
  end

  structure pequiv (A B : Pointed) :=
    (to_pmap : A →* B)
    (is_equiv_to_pmap : is_equiv to_pmap)

  infix `≃*`:25 := pequiv
  attribute pequiv.to_pmap [coercion]
  attribute pequiv.is_equiv_to_pmap [instance]

  definition equiv_of_pequiv [constructor] (f : A ≃* B) : A ≃ B :=
  equiv.mk f _

end pointed
