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

  definition pt [unfold-c 2] [H : pointed A] := point A
  protected abbreviation Mk [constructor] := @Pointed.mk
  protected definition mk' [constructor] (A : Type) [H : pointed A] : Pointed :=
  Pointed.mk (point A)
  definition pointed_carrier [instance] [constructor] (A : Pointed) : pointed A :=
  pointed.mk (Point A)

  -- Any contractible type is pointed
  definition pointed_of_is_contr [instance] [constructor] (A : Type) [H : is_contr A] : pointed A :=
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

  definition Iterated_loop_space (A : Pointed) (n : ℕ) : Pointed :=
  nat.rec_on n (λA, A) (λn IH A, IH (Loop_space A)) A

  prefix `Ω`:(max+1) := Loop_space
  notation `Ω[`:95 n:0 `]`:0 A:95 := Iterated_loop_space A n

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
structure pointed_map (A B : Pointed) :=
  (map : A → B) (respect_pt : map (Point A) = Point B)

open pointed_map

namespace pointed

  abbreviation respect_pt := @pointed_map.respect_pt

  -- definition transport_to_sigma {A B : Pointed}
  --   {P : Π(X : Type) (m : X → A → B), (Π(f : X), m f (Point A) = Point B) → (Π(m : A → B), m (Point A) = Point B → X) →  Type}
  --   (H : P (Σ(f : A → B), f (Point A) = Point B) pr1 pr2 sigma.mk) :
  --   P (pointed_map A B) map respect_pt pointed_map.mk :=
  -- sorry


  notation `map₊` := pointed_map
  attribute pointed_map.map [coercion]
  definition pointed_map_eq {A B : Pointed} {f g : map₊ A B}
    (r : Πa, f a = g a) (s : respect_pt f = (r pt) ⬝ respect_pt g) : f = g :=
  begin
    cases f with f p, cases g with g q,
    esimp at *,
    fapply apo011 pointed_map.mk,
    { exact eq_of_homotopy r},
    { apply concato_eq, apply pathover_eq_Fl, apply inv_con_eq_of_eq_con,
      rewrite [ap_eq_ap10,↑ap10,apd10_eq_of_homotopy,↑respect_pt at *,s]}
  end

  definition pointed_map_equiv_left (A : Type) (B : Pointed) : map₊ A₊ B ≃ (A → B) :=
  begin
    fapply equiv.MK,
    { intro f a, cases f with f p, exact f (some a)},
    { intro f, fapply pointed_map.mk,
        intro a, cases a, exact pt, exact f a,
        reflexivity},
    { intro f, reflexivity},
    { intro f, cases f with f p, esimp, fapply pointed_map_eq,
      { intro a, cases a; all_goals (esimp at *), exact p⁻¹},
      { esimp, exact !con.left_inv⁻¹}},
  end

  -- set_option pp.notation false
  -- definition pointed_map_equiv_right (A : Pointed) (B : Type)
  --   : (Σ(b : B), map₊ A (pointed.Mk b)) ≃ (A → B) :=
  -- begin
  --   fapply equiv.MK,
  --   { intro u a, cases u with b f, cases f with f p, esimp at f, exact f a},
  --   { intro f, refine ⟨f pt, _⟩, fapply pointed_map.mk,
  --       intro a, esimp, exact f a,
  --       reflexivity},
  --   { intro f, reflexivity},
  --   { intro u, cases u with b f, cases f with f p, esimp at *, apply sigma_eq p,
  --     esimp, apply sorry
  --     }
  -- end


  definition pointed_map_bool_equiv (B : Pointed) : map₊ Bool B ≃ B :=
  begin
    fapply equiv.MK,
    { intro f, cases f with f p, exact f tt},
    { intro b, fapply pointed_map.mk,
        intro u, cases u, exact pt, exact b,
        reflexivity},
    { intro b, reflexivity},
    { intro f, cases f with f p, esimp, fapply pointed_map_eq,
      { intro a, cases a; all_goals (esimp at *), exact p⁻¹},
      { esimp, exact !con.left_inv⁻¹}},
  end
  -- calc
  --   map₊ (Pointed.mk' bool) B ≃ map₊ unit₊ B : sorry
  --     ... ≃ (unit → B) : pointed_map_equiv
  --     ... ≃ B : unit_imp_equiv

end pointed
