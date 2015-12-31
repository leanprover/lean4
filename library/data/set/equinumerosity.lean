/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Two sets are equinumerous, or equipollent, if there is a bijection between them. It is sometimes
said that two such sets "have the same cardinality."
-/
import .classical_inverse data.nat
open eq.ops classical nat

/- two versions of Cantor's theorem -/

namespace set

variables {X : Type} {A : set X}

theorem not_surj_on_pow (f : X → set X) : ¬ surj_on f A (𝒫 A) :=
let diag := {x ∈ A | x ∉ f x} in
have diag ⊆ A, from sep_subset _ _,
assume H : surj_on f A (𝒫 A),
obtain x [(xA : x ∈ A) (Hx : f x = diag)], from H `diag ⊆ A`,
have x ∉ f x, from
  suppose x ∈ f x,
  have x ∈ diag, from Hx ▸ this,
  have x ∉ f x, from and.right this,
  show false, from this `x ∈ f x`,
have x ∈ diag, from and.intro xA this,
have x ∈ f x, from Hx⁻¹ ▸ this,
show false, from `x ∉ f x` this

theorem not_inj_on_pow {f : set X → X} (H : maps_to f (𝒫 A) A) : ¬ inj_on f (𝒫 A) :=
let diag := f '[{x ∈ 𝒫 A | f x ∉ x}] in
have diag ⊆ A, from image_subset_of_maps_to_of_subset H (sep_subset _ _),
assume H₁ : inj_on f (𝒫 A),
have f diag ∈ diag, from by_contradiction
  (suppose f diag ∉ diag,
    have diag ∈ {x ∈ 𝒫 A | f x ∉ x}, from and.intro `diag ⊆ A` this,
    have f diag ∈ diag, from mem_image_of_mem f this,
    show false, from `f diag ∉ diag` this),
obtain x [(Hx : x ∈ 𝒫 A ∧ f x ∉ x) (fxeq : f x = f diag)], from this,
have x = diag, from H₁ (and.left Hx) `diag ⊆ A` fxeq,
have f diag ∉ diag, from this ▸ and.right Hx,
show false, from this `f diag ∈ diag`

end set

/-
The Schröder-Bernstein theorem. The proof below is nonconstructive, in three ways:
(1) We need a left inverse to g (we could get around this by supplying one).
(2) The definition of h below assumes that membership in Union U is decidable.
(3) We ultimately case split on whether B is empty, and choose an element if it isn't.

Rather than mark every auxiliary construction as "private", we put them all in a
separate namespace.
-/

namespace schroeder_bernstein
section
open set
  parameters {X Y : Type}
  parameter  {A : set X}
  parameter  {B : set Y}
  parameter  {f : X → Y}
  parameter  (f_maps_to : maps_to f A B)
  parameter  (finj : inj_on f A)
  parameter  {g : Y → X}
  parameter  (g_maps_to : maps_to g B A)
  parameter  (ginj : inj_on g B)
  parameter  {dflt : Y}                    -- for now, assume B is nonempty
  parameter  (dfltB : dflt ∈ B)

  /- g⁻¹ : A → B -/

  noncomputable definition ginv : X → Y := inv_fun g B dflt

  lemma ginv_maps_to : maps_to ginv A B :=
  maps_to_inv_fun dfltB

  lemma ginv_g_eq {b : Y} (bB : b ∈ B) : ginv (g b) = b :=
  left_inv_on_inv_fun_of_inj_on dflt ginj bB

  /- define a sequence of sets U -/

  definition U : ℕ → set X
  | U 0       := A \ g '[B]
  | U (n + 1) := g '[f '[U n]]

  lemma U_subset_A : ∀ n, U n ⊆ A
  | 0       := show U 0 ⊆ A,
                 from diff_subset _ _
  | (n + 1) := have f '[U n] ⊆ B,
                 from image_subset_of_maps_to_of_subset f_maps_to (U_subset_A n),
               show U (n + 1) ⊆ A,
                 from image_subset_of_maps_to_of_subset g_maps_to this

  lemma g_ginv_eq {a : X} (aA : a ∈ A) (anU  : a ∉ Union U) : g (ginv a) = a :=
  have a ∈ g '[B], from by_contradiction
    (suppose a ∉ g '[B],
      have a ∈ U 0, from and.intro aA this,
      have a ∈ Union U, from exists.intro 0 this,
      show false, from anU this),
  obtain b [(bB : b ∈ B) (gbeq : g b = a)], from this,
  calc
    g (ginv a) = g (ginv (g b)) : gbeq
           ... = g b            : ginv_g_eq bB
           ... = a              : gbeq

  /- h : A → B -/

  noncomputable definition h x := if x ∈ Union U then f x else ginv x

  lemma h_maps_to : maps_to h A B :=
  take a,
  suppose a ∈ A,
  show h a ∈ B, from
    by_cases
      (suppose a ∈ Union U,
        by+ rewrite [↑h, if_pos this]; exact f_maps_to `a ∈ A`)
      (suppose a ∉ Union U,
        by+ rewrite [↑h, if_neg this]; exact ginv_maps_to `a ∈ A`)

  /- h is injective -/

  lemma aux {a₁ a₂ : X} (H₁ : a₁ ∈ Union U) (a₂A : a₂ ∈ A) (heq : h a₁ = h a₂) : a₂ ∈ Union U :=
  obtain n (a₁Un : a₁ ∈ U n), from H₁,
  have ha₁eq : h a₁ = f a₁,
    from dif_pos H₁,
  show a₂ ∈ Union U, from by_contradiction
    (suppose a₂ ∉ Union U,
      have ha₂eq : h a₂ = ginv a₂,
        from dif_neg this,
      have g (f a₁) = a₂, from calc
        g (f a₁) = g (h a₁)       : ha₁eq
             ... = g (h a₂)       : heq
             ... = g (ginv a₂)    : ha₂eq
             ... = a₂             : g_ginv_eq a₂A `a₂ ∉ Union U`,
      have g (f a₁) ∈ g '[f '[U n]],
        from mem_image_of_mem g (mem_image_of_mem f a₁Un),
      have a₂ ∈ U (n + 1),
        from `g (f a₁) = a₂` ▸ this,
      have a₂ ∈ Union U,
        from exists.intro _ this,
      show false, from `a₂ ∉ Union U` `a₂ ∈ Union U`)

  lemma h_inj : inj_on h A :=
  take a₁ a₂,
  suppose a₁ ∈ A,
  suppose a₂ ∈ A,
  assume heq : h a₁ = h a₂,
  show a₁ = a₂, from
  by_cases
    (assume a₁UU : a₁ ∈ Union U,
      have a₂UU : a₂ ∈ Union U,
        from aux a₁UU `a₂ ∈ A` heq,
      have f a₁ = f a₂, from calc
        f a₁ = h a₁ : dif_pos a₁UU
          ... = h a₂ : heq
          ... = f a₂ : dif_pos a₂UU,
      show a₁ = a₂, from
        finj `a₁ ∈ A` `a₂ ∈ A` this)
    (assume a₁nUU : a₁ ∉ Union U,
      have a₂nUU : a₂ ∉ Union U,
        from assume H, a₁nUU (aux H `a₁ ∈ A` heq⁻¹),
      have eq₁ : g (ginv a₁) = a₁, from g_ginv_eq `a₁ ∈ A` a₁nUU,
      have eq₂ : g (ginv a₂) = a₂, from g_ginv_eq `a₂ ∈ A` a₂nUU,
      have ginv a₁ = ginv a₂, from calc
        ginv a₁ = h a₁ : dif_neg a₁nUU
            ... = h a₂ : heq
            ... = ginv a₂ : dif_neg a₂nUU,
      show a₁ = a₂, from calc
        a₁    = g (ginv a₁) : eq₁ -- g_ginv_eq `a₁ ∈ A` a₁nUU
          ... = g (ginv a₂) : this
          ... = a₂          : eq₂) -- g_ginv_eq `a₂ ∈ A` a₂nUU)

  /- h is surjective -/

  lemma h_surj : surj_on h A B :=
  take b,
  suppose b ∈ B,
  have g b ∈ A, from g_maps_to this,
  by_cases
    (suppose g b ∈ Union U,
       obtain n (gbUn : g b ∈ U n), from this,
      using ginj f_maps_to,
      begin
        cases n with n,
          {have g b ∈ U 0, from gbUn,
            have g b ∉ g '[B], from and.right this,
            have g b ∈ g '[B], from mem_image_of_mem g `b ∈ B`,
            show b ∈ h '[A], from absurd `g b ∈ g '[B]` `g b ∉ g '[B]`},
        {have g b ∈ U (succ n), from gbUn,
           have g b ∈ g '[f '[U n]], from this,
           obtain b' [(b'fUn : b' ∈ f '[U n]) (geq : g b' = g b)], from this,
           obtain a [(aUn : a ∈ U n) (faeq : f a = b')], from b'fUn,
           have g (f a) = g b, by rewrite [faeq, geq],
           have a ∈ A, from U_subset_A n aUn,
           have f a ∈ B, from f_maps_to this,
           have f a = b, from ginj `f a ∈ B` `b ∈ B` `g (f a) = g b`,
           have a ∈ Union U, from exists.intro n aUn,
           have h a = f a, from dif_pos this,
           show b ∈ h '[A], from mem_image `a ∈ A` (`h a = f a` ⬝ `f a = b`)}
      end)
    (suppose g b ∉ Union U,
      have eq₁ : h (g b) = ginv (g b), from dif_neg this,
      have eq₂ : ginv (g b) = b, from ginv_g_eq `b ∈ B`,
      show b ∈ h '[A], from mem_image `g b ∈ A` (eq₁ ⬝ eq₂))
end
end schroeder_bernstein

namespace set
section
  parameters {X Y : Type}
  parameter  {A : set X}
  parameter  {B : set Y}
  parameter  {f : X → Y}
  parameter  (f_maps_to : maps_to f A B)
  parameter  (finj : inj_on f A)
  parameter  {g : Y → X}
  parameter  (g_maps_to : maps_to g B A)
  parameter  (ginj : inj_on g B)

  theorem schroeder_bernstein : ∃ h, bij_on h A B :=
  by_cases
    (assume H : ∀ b, b ∉ B,
      have fsurj : surj_on f A B, from take b, suppose b ∈ B, absurd this !H,
      exists.intro f (and.intro f_maps_to (and.intro finj fsurj)))
    (assume H : ¬ ∀ b, b ∉ B,
      have ∃ b, b ∈ B, from exists_of_not_forall_not H,
      obtain b bB, from this,
      let h := @schroeder_bernstein.h X Y A B f g b in
      have h_maps_to : maps_to h A B, from schroeder_bernstein.h_maps_to f_maps_to bB,
      have hinj : inj_on h A, from schroeder_bernstein.h_inj finj ginj, -- ginj,
      have hsurj : surj_on h A B, from schroeder_bernstein.h_surj f_maps_to g_maps_to ginj,
      exists.intro h (and.intro h_maps_to (and.intro hinj hsurj)))
end
end set
