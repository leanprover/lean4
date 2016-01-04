/-
Copyright (c) 2016 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Galois connections - order theoretic adjoints.
-/
import standard
open classical eq.ops algebra set function complete_lattice

/- Move to set? -/
definition kern_image {X Y : Type} (f : X → Y) (S : set X) : set Y := {y | ∀x, f x = y → x ∈ S }

/- Order theoretic definitions -/

/- TODO: move to order? -/
section order
variables {A B : Type} {S : set A} {a a' : A} {b b' : B} {f : A → B} [weak_order A] [weak_order B]

definition increasing (f : A → A) := ∀⦃a⦄, a ≤ f a
definition decreasing (f : A → A) := ∀⦃a⦄, f a ≤ a

definition upper_bounds (S : set A) : set A := { x | ∀₀ s ∈ S, s ≤ x }
definition lower_bounds (S : set A) : set A := { x | ∀₀ s ∈ S, x ≤ s }
definition is_least (S : set A) (a : A) := a ∈ S ∧ a ∈ lower_bounds S
definition is_greatest (S : set A) (a : A) := a ∈ S ∧ a ∈ upper_bounds S

definition monotone (f : A → B) := ∀⦃a b⦄, a ≤ b → f a ≤ f b

lemma is_least_unique (Ha : is_least S a) (Hb : is_least S a') : a = a' :=
le.antisymm
  begin apply (and.elim_right Ha), apply (and.elim_left Hb) end
  begin apply (and.elim_right Hb), apply (and.elim_left Ha) end

lemma is_least_unique_iff (Ha : is_least S a) : is_least S a' ↔ a = a' :=
iff.intro (is_least_unique Ha) begin intro H, cases H, apply Ha end

lemma is_greatest_unique (Ha : is_greatest S a) (Hb : is_greatest S a') : a = a' :=
le.antisymm
  begin apply (and.elim_right Hb), apply (and.elim_left Ha) end
  begin apply (and.elim_right Ha), apply (and.elim_left Hb) end

lemma is_greatest_unique_iff (Ha : is_greatest S a) : is_greatest S a' ↔ a = a' :=
iff.intro (is_greatest_unique Ha) begin intro H, cases H, apply Ha end

definition is_lub (S : set A) := is_least (upper_bounds S)
definition is_glb (S : set A) := is_greatest (lower_bounds S)

lemma is_lub_unique : is_lub S a → is_lub S a' → a = a' :=
!is_least_unique

lemma is_lub_unique_iff : is_lub S a → (is_lub S a' ↔ a = a') :=
!is_least_unique_iff

lemma is_glb_unique : is_glb S a → is_glb S a' → a = a' :=
!is_greatest_unique

lemma is_glb_unique_iff : is_glb S a → (is_glb S a' ↔ a = a') :=
!is_greatest_unique_iff

lemma upper_bounds_image (Hf : monotone f) (Ha : a ∈ upper_bounds S) : f a ∈ upper_bounds (f ' S) :=
forall_image_implies_forall (take x H, Hf (Ha `x ∈ S`))

lemma lower_bounds_image (Hf : monotone f) (Ha : a ∈ lower_bounds S) : f a ∈ lower_bounds (f ' S) :=
forall_image_implies_forall (take x H, Hf (Ha `x ∈ S`))

end order

definition galois_connection {A B : Type} [weak_order A] [weak_order B] (l : A → B) (u : B → A) :=
  ∀{a b}, l a ≤ b ↔ a ≤ u b

namespace galois_connection

section
parameters {A B : Type} [weak_order A] [weak_order B] (l : A → B) (u : B → A)

lemma monotone_intro (Mu : monotone u) (Ml : monotone l)
    (Iul : increasing (u ∘ l)) (Dlu : decreasing (l ∘ u)) : galois_connection l u :=
begin
  intros a b,
  apply iff.intro,
  { intro H, apply le.trans, apply Iul, apply Mu, assumption },
  { intro H, apply le.trans, apply Ml, assumption, apply Dlu }
end

parameter (gc : galois_connection l u)
include gc

lemma l_le {a : A} {b : B} : a ≤ u b → l a ≤ b :=
and.elim_right !gc

lemma le_u {a : A} {b : B} : l a ≤ b → a ≤ u b :=
and.elim_left !gc

lemma increasing_u_l : increasing (u ∘ l) :=
take a, le_u !le.refl

lemma decreasing_l_u : decreasing (l ∘ u) :=
take a, l_le !le.refl

lemma monotone_u : monotone u :=
take a b H, le_u (le.trans !decreasing_l_u H)

lemma monotone_l : monotone l :=
take a b H, l_le (le.trans H !increasing_u_l)

lemma u_l_u_eq_u : u ∘ l ∘ u = u :=
funext (take x, le.antisymm (monotone_u !decreasing_l_u) !increasing_u_l)

lemma l_u_l_eq_l : l ∘ u ∘ l = l :=
funext (take x, le.antisymm !decreasing_l_u (monotone_l !increasing_u_l))

lemma u_upper_bounds {S : set A} {b : B} (H : b ∈ upper_bounds (l ' S)) : u b ∈ upper_bounds S :=
take c, suppose c ∈ S, le_u (H (!mem_image_of_mem `c ∈ S`))

lemma l_lower_bounds {S : set B} {a : A} (H : a ∈ lower_bounds (u ' S)) : l a ∈ lower_bounds S :=
take c, suppose c ∈ S, l_le (H (!mem_image_of_mem `c ∈ S`))

lemma l_preserves_lub {S : set A} {a : A} (H : is_lub S a) : is_lub (l ' S) (l a) :=
and.intro
  (upper_bounds_image monotone_l (and.elim_left `is_lub S a`))
  (take b Hb, l_le (and.elim_right `is_lub S a` _ (u_upper_bounds Hb)))

lemma u_preserves_glb {S : set B} {b : B} (H : is_glb S b) : is_glb (u ' S) (u b) :=
and.intro
  (lower_bounds_image monotone_u (and.elim_left `is_glb S b`))
  (take a Ha, le_u (and.elim_right `is_glb S b` _ (l_lower_bounds Ha)))

lemma l_is_glb {a : A} : is_glb { b | a ≤ u b } (l a) :=
begin
  apply and.intro,
  { intro b, apply l_le },
  { intro b H, apply H, apply increasing_u_l }  
end

lemma u_is_lub {b : B} : is_lub { a | l a ≤ b } (u b) :=
begin
  apply and.intro,
  { intro a, apply le_u },
  { intro a H, apply H, apply decreasing_l_u }  
end

end

/- Constructing Galois connections -/

lemma id {A : Type} [weak_order A] : @galois_connection A A _ _ id id :=
take a b, iff.intro (λx, x) (λx, x)

lemma dual {A B : Type} [woA : weak_order A] [woB : weak_order B]
  (l : A → B) (u : B → A) (gc : galois_connection l u) :
  @galois_connection B A (weak_order_dual woB) (weak_order_dual woA) u l :=
take a b,
begin
  apply iff.symm,
  rewrite dual,
  rewrite dual,  
  exact gc, 
end

lemma compose {A B C : Type} [weak_order A] [weak_order B] [weak_order C]
  (l1 : A → B) (u1 : B → A) (l2 : B → C) (u2 : C → B)
  (gc1 : galois_connection l1 u1) (gc2 : galois_connection l2 u2) :
  galois_connection (l2 ∘ l1) (u1 ∘ u2) :=
by intros; rewrite gc2; rewrite gc1

section 
  variables {A B : Type} {f : A → B}

  lemma image_preimage : galois_connection (image f) (preimage f) :=
    @image_subset_iff A B f

  lemma preimage_kern_image : galois_connection (preimage f) (kern_image f) :=
  begin
    intros X Y, apply iff.intro, all_goals (intro H x Hx),
    { intro x' eq, apply H, cases eq, exact Hx },
    { apply H,
      esimp [preimage, mem, set_of] at Hx, exact Hx, -- TODO: why is esimp necessary?
      exact rfl }
  end
end

end galois_connection

/- Bounds on complete lattices -/
/- TODO: move to complete lattices? -/

section
variables {A : Type} (S : set A) {a b : A} [complete_lattice A]

lemma is_lub_sup : is_lub '{a, b} (sup a b) :=
and.intro
  begin
    xrewrite [+forall_insert_iff, bounded_forall_empty_iff, and_true],
    exact (and.intro !le_sup_left !le_sup_right)
  end
  begin
    intro x Hx,
    xrewrite [+forall_insert_iff at Hx, bounded_forall_empty_iff at Hx, and_true at Hx],
    apply sup_le,
    apply (and.elim_left Hx),
    apply (and.elim_right Hx),
  end

lemma is_lub_Sup : is_lub S (⨆S) :=
and.intro (take x, le_Sup) (take x, Sup_le)

lemma is_lub_Sup_iff {a : A} : is_lub S a ↔ (⨆S) = a :=
!is_lub_unique_iff !is_lub_Sup

lemma is_glb_Inf : is_glb S (⨅S) :=
and.intro (take a, Inf_le) (take a, le_Inf)

lemma is_glb_Inf_iff : is_glb S a ↔ (⨅S) = a :=
!is_glb_unique_iff !is_glb_Inf

end
