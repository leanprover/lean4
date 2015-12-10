/-
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Floris van Doorn

Ported from Coq HoTT
-/

import arity .eq .bool .unit .sigma .nat.basic
open is_trunc eq prod sigma nat equiv option is_equiv bool unit algebra

structure pointed [class] (A : Type) :=
  (point : A)

structure Pointed :=
  {carrier : Type}
  (Point   : carrier)

open Pointed

notation `Type*` := Pointed

namespace pointed
  attribute Pointed.carrier [coercion]
  variables {A B : Type}

  definition pt [unfold 2] [H : pointed A] := point A
  protected definition Mk [constructor] := @Pointed.mk
  protected definition MK [constructor] (A : Type) (a : A) := Pointed.mk a
  protected definition mk' [constructor] (A : Type) [H : pointed A] : Type* :=
  Pointed.mk (point A)
  definition pointed_carrier [instance] [constructor] (A : Type*) : pointed A :=
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

  definition Bool [constructor] : Type* :=
  pointed.mk' bool

  definition Unit [constructor] : Type* :=
  Pointed.mk unit.star

  definition pointed_fun_closed [constructor] (f : A → B) [H : pointed A] : pointed B :=
  pointed.mk (f pt)

  definition Loop_space [reducible] [constructor] (A : Type*) : Type* :=
  pointed.mk' (point A = point A)

  definition Iterated_loop_space [unfold 1] [reducible] : ℕ → Type* → Type*
  | Iterated_loop_space  0    X := X
  | Iterated_loop_space (n+1) X := Loop_space (Iterated_loop_space n X)

  prefix `Ω`:(max+5) := Loop_space
  notation `Ω[`:95 n:0 `] `:0 A:95 := Iterated_loop_space n A

  definition rfln  [constructor] [reducible] {A : Type*} {n : ℕ} : Ω[n] A := pt
  definition refln [constructor] [reducible] (A : Type*) (n : ℕ) : Ω[n] A := pt
  definition refln_eq_refl (A : Type*) (n : ℕ) : rfln = rfl :> Ω[succ n] A := rfl

  definition iterated_loop_space [unfold 3] (A : Type) [H : pointed A] (n : ℕ) : Type :=
  Ω[n] (pointed.mk' A)

  open equiv.ops
  definition Pointed_eq {A B : Type*} (f : A ≃ B) (p : f pt = pt) : A = B :=
  begin
    cases A with A a, cases B with B b, esimp at *,
    fapply apd011 @Pointed.mk,
    { apply ua f},
    { rewrite [cast_ua,p]},
  end

  protected definition Pointed.sigma_char.{u} : Pointed.{u} ≃ Σ(X : Type.{u}), X :=
  begin
    fapply equiv.MK,
    { intro x, induction x with X x, exact ⟨X, x⟩},
    { intro x, induction x with X x, exact pointed.MK X x},
    { intro x, induction x with X x, reflexivity},
    { intro x, induction x with X x, reflexivity},
  end


  definition add_point [constructor] (A : Type) : Type* :=
  Pointed.mk (none : option A)
  postfix `₊`:(max+1) := add_point
  -- the inclusion A → A₊ is called "some", the extra point "pt" or "none" ("@none A")
end pointed

open pointed
structure pmap (A B : Type*) :=
  (map : A → B)
  (resp_pt : map (Point A) = Point B)

open pmap

namespace pointed

  abbreviation respect_pt [unfold 3] := @pmap.resp_pt
  notation `map₊` := pmap
  infix ` →* `:30 := pmap
  attribute pmap.map [coercion]
  variables {A B C D : Type*} {f g h : A →* B}

  definition pmap_eq (r : Πa, f a = g a) (s : respect_pt f = (r pt) ⬝ respect_pt g) : f = g :=
  begin
    cases f with f p, cases g with g q,
    esimp at *,
    fapply apo011 pmap.mk,
    { exact eq_of_homotopy r},
    { apply concato_eq, apply pathover_eq_Fl, apply inv_con_eq_of_eq_con,
      rewrite [ap_eq_ap10,↑ap10,apd10_eq_of_homotopy,s]}
  end

  definition pid [constructor] (A : Type*) : A →* A :=
  pmap.mk id idp

  definition pcompose [constructor] (g : B →* C) (f : A →* B) : A →* C :=
  pmap.mk (λa, g (f a)) (ap g (respect_pt f) ⬝ respect_pt g)

  infixr ` ∘* `:60 := pcompose

  structure phomotopy (f g : A →* B) :=
    (homotopy : f ~ g)
    (homotopy_pt : homotopy pt ⬝ respect_pt g = respect_pt f)

  infix ` ~* `:50 := phomotopy
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

  definition pmap_equiv_left (A : Type) (B : Type*) : A₊ →* B ≃ (A → B) :=
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

  -- set_option pp.notation false
  -- definition pmap_equiv_right (A : Type*) (B : Type)
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

  definition pmap_bool_equiv (B : Type*) : map₊ Bool B ≃ B :=
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

  definition ap1 [constructor] (f : A →* B) : Ω A →* Ω B :=
  begin
    fconstructor,
    { intro p, exact !respect_pt⁻¹ ⬝ ap f p ⬝ !respect_pt},
    { esimp, apply con.left_inv}
  end

  definition apn [unfold 3] (n : ℕ) (f : map₊ A B) : Ω[n] A →* Ω[n] B :=
  begin
  induction n with n IH,
  { exact f},
  { esimp [Iterated_loop_space], exact ap1 IH}
  end

  variable (A)
  definition loop_space_succ_eq_in (n : ℕ) : Ω[succ n] A = Ω[n] (Ω A) :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact ap Loop_space IH}
  end

  definition loop_space_add (n m : ℕ) : Ω[n] (Ω[m] A) = Ω[m+n] (A) :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact ap Loop_space IH}
  end

  definition loop_space_succ_eq_out (n : ℕ) : Ω[succ n] A = Ω(Ω[n] A)  :=
  idp

  variable {A}

  /- the equality [loop_space_succ_eq_in] preserves concatenation -/
  theorem loop_space_succ_eq_in_concat {n : ℕ} (p q : Ω[succ (succ n)] A) :
           transport carrier (ap Loop_space (loop_space_succ_eq_in A n)) (p ⬝ q)
         = transport carrier (ap Loop_space (loop_space_succ_eq_in A n)) p
         ⬝ transport carrier (ap Loop_space (loop_space_succ_eq_in A n)) q :=
  begin
    rewrite [-+tr_compose, ↑function.compose],
    rewrite [+@transport_eq_FlFr_D _ _ _ _ Point Point, +con.assoc], apply whisker_left,
    rewrite [-+con.assoc], apply whisker_right, rewrite [con_inv_cancel_right, ▸*, -ap_con]
  end

  definition loop_space_loop_irrel (p : point A = point A) : Ω(Pointed.mk p) = Ω[2] A :=
  begin
    intros, fapply Pointed_eq,
    { esimp, transitivity _,
      apply eq_equiv_fn_eq_of_equiv (equiv_eq_closed_right _ p⁻¹),
      esimp, apply eq_equiv_eq_closed, apply con.right_inv, apply con.right_inv},
    { esimp, apply con.left_inv}
  end

  definition iterated_loop_space_loop_irrel (n : ℕ) (p : point A = point A)
    : Ω[succ n](Pointed.mk p) = Ω[succ (succ n)] A :> Pointed :=
  calc
    Ω[succ n](Pointed.mk p) = Ω[n](Ω (Pointed.mk p)) : loop_space_succ_eq_in
      ... = Ω[n] (Ω[2] A)                            : loop_space_loop_irrel
      ... = Ω[2+n] A                                 : loop_space_add
      ... = Ω[n+2] A                                 : by rewrite [algebra.add.comm]

  -- TODO:
  -- definition apn_compose (n : ℕ) (g : B →* C) (f : A →* B) : apn n (g ∘* f) ~* apn n g ∘* apn n f :=
  -- _

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

  infix ` ⬝* `:75 := phomotopy.trans
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

  structure pequiv (A B : Type*) :=
    (to_pmap : A →* B)
    (is_equiv_to_pmap : is_equiv to_pmap)

  infix ` ≃* `:25 := pequiv
  attribute pequiv.to_pmap [coercion]
  attribute pequiv.is_equiv_to_pmap [instance]

  definition equiv_of_pequiv [constructor] (f : A ≃* B) : A ≃ B :=
  equiv.mk f _

  definition to_pinv [constructor] (f : A ≃* B) : B →* A :=
  pmap.mk f⁻¹ (ap f⁻¹ (respect_pt f)⁻¹ ⬝ !left_inv)

  definition pua {A B : Type*} (f : A ≃* B) : A = B :=
  Pointed_eq (equiv_of_pequiv f) !respect_pt


end pointed
