/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Filters, following Hölzl, Immler, and Huffman, "Type classes and filters for mathematical
analysis in Isabelle/HOL".
-/
import data.set.function logic.identities algebra.complete_lattice
namespace set
open classical

structure filter (A : Type) :=
(sets           : set (set A))
(univ_mem_sets  : univ ∈ sets)
(inter_closed   : ∀ {a b}, a ∈ sets → b ∈ sets → a ∩ b ∈ sets)
(is_mono        : ∀ {a b}, a ⊆ b → a ∈ sets → b ∈ sets)

attribute filter.sets [coercion]

namespace filter -- i.e. set.filter

variable {A : Type}
variables {P Q : A → Prop}
variables {F₁ : filter A} {F₂ : filter A} {F : filter A}

definition eventually (P : A → Prop) (F : filter A) : Prop :=
P ∈ F

-- TODO: notation for eventually?
-- notation `forallf` binders `∈` F `,` r:(scoped:1 P, P) := eventually r F
-- notation `'∀f` binders `∈` F `,` r:(scoped:1 P, P) := eventually r F

theorem eventually_true (F : filter A) : eventually (λx, true) F :=
!filter.univ_mem_sets

theorem eventually_of_forall {P : A → Prop} (F : filter A) (H : ∀ x, P x) : eventually P F :=
by rewrite [eq_univ_of_forall H]; apply eventually_true

theorem eventually_mono (H₁ : eventually P F) (H₂ : ∀x, P x → Q x) : eventually Q F :=
!filter.is_mono H₂ H₁

theorem eventually_and (H₁ : eventually P F) (H₂ : eventually Q F) :
  eventually (λ x, P x ∧ Q x) F :=
!filter.inter_closed H₁ H₂

theorem eventually_mp (H₁ : eventually (λx, P x → Q x) F) (H₂ : eventually P F) :
  eventually Q F :=
have ∀ x, (P x → Q x) ∧ P x → Q x, from take x, assume H, and.left H (and.right H),
eventually_mono (eventually_and H₁ H₂) this

theorem eventually_mpr (H₁ : eventually P F) (H₂ : eventually (λx, P x → Q x) F) :
  eventually Q F := eventually_mp H₂ H₁

variables (P Q F)
theorem eventually_and_iff : eventually (λ x, P x ∧ Q x) F ↔ eventually P F ∧ eventually Q F :=
iff.intro
  (assume H, and.intro
    (eventually_mpr H (eventually_of_forall F (take x, and.left)))
    (eventually_mpr H (eventually_of_forall F (take x, and.right))))
  (assume H, eventually_and (and.left H) (and.right H))
variables {P Q F}

-- TODO: port eventually_ball_finite_distrib, etc.

theorem eventually_choice {B : Type} [nonemptyB : nonempty B] {R : A → B → Prop} {F : filter A}
  (H : eventually (λ x, ∃ y, R x y) F) : ∃ f, eventually (λ x, R x (f x)) F :=
let f := λ x, epsilon (λ y, R x y) in
exists.intro f
  (eventually_mono H
    (take x, suppose ∃ y, R x y,
      show R x (f x), from epsilon_spec this))

theorem exists_not_of_not_eventually (H : ¬ eventually P F) : ∃ x, ¬ P x :=
exists_not_of_not_forall (assume H', H (eventually_of_forall F H'))

theorem eventually_iff_mp (H₁ : eventually (λ x, P x ↔ Q x) F) (H₂ : eventually P F) :
  eventually Q F :=
eventually_mono (eventually_and H₁ H₂) (λ x H, iff.mp (and.left H) (and.right H))

theorem eventually_iff_mpr (H₁ : eventually (λ x, P x ↔ Q x) F) (H₂ : eventually Q F) :
  eventually P F :=
eventually_mono (eventually_and H₁ H₂) (λ x H, iff.mpr (and.left H) (and.right H))

theorem eventually_iff_iff (H : eventually (λ x, P x ↔ Q x) F) : eventually P F ↔ eventually Q F :=
iff.intro (eventually_iff_mp H) (eventually_iff_mpr H)

-- TODO: port frequently and properties?

/- filters form a lattice under ⊇ -/

protected theorem eq : sets F₁ = sets F₂ → F₁ = F₂ :=
begin
  cases F₁ with s₁ u₁ i₁ m₁, cases F₂ with s₂ u₂ i₂ m₂, esimp,
  intro eqs₁s₂, revert [u₁, i₁, m₁, u₂, i₂, m₂],
  subst s₁, intros, exact rfl
end

definition weakens [reducible] (F₁ F₂ : filter A) := F₁ ⊇ F₂
infix `≼`:50 := weakens

definition refines [reducible] (F₁ F₂ : filter A) := F₁ ⊆ F₂
infix `≽`:50 := refines

theorem weakens.refl (F : filter A) : F ≼ F := subset.refl _

theorem weakens.trans {F₁ F₂ F₃ : filter A} (H₁ : F₁ ≼ F₂) (H₂ : F₂ ≼ F₃) : F₁ ≼ F₃ :=
subset.trans H₂ H₁

theorem weakens.antisymm (H₁ : F₁ ≼ F₂) (H₂ : F₂ ≼ F₁) : F₁ = F₂ :=
filter.eq (eq_of_subset_of_subset H₂ H₁)

definition bot : filter A :=
⦃ filter,
  sets           := univ,
  univ_mem_sets  := trivial,
  inter_closed := λ a b Ha Hb, trivial,
  is_mono        := λ a b Ha Hsub, trivial
⦄
notation `⊥` := bot

definition top : filter A :=
⦃ filter,
  sets          := '{univ},
  univ_mem_sets := !or.inl rfl,
  inter_closed  := abstract
                     λ a b Ha Hb,
                     by rewrite [*!mem_singleton_iff at *]; substvars; exact !inter_univ
                   end,
  is_mono       := abstract
                     λ a b Hsub Ha,
                     begin
                       rewrite [mem_singleton_iff at Ha], subst [Ha],
                       exact or.inl (eq_univ_of_univ_subset Hsub)
                     end
                   end
⦄
notation `⊤` := top

definition sup (F₁ F₂ : filter A) : filter A :=
⦃ filter,
  sets          := F₁ ∩ F₂,
  univ_mem_sets := and.intro (filter.univ_mem_sets F₁) (filter.univ_mem_sets F₂),
  inter_closed  := abstract
                     λ a b Ha Hb,
                     and.intro
                       (filter.inter_closed F₁ (and.left Ha) (and.left Hb))
                       (filter.inter_closed F₂ (and.right Ha) (and.right Hb))
                     end,
  is_mono       := abstract
                     λ a b Hsub Ha,
                     and.intro
                       (filter.is_mono F₁ Hsub (and.left Ha))
                       (filter.is_mono F₂ Hsub (and.right Ha))
                     end
⦄
infix `⊔`:65 := sup

definition inf (F₁ F₂ : filter A) : filter A :=
⦃ filter,
  sets          := {r | ∃₀ s ∈ F₁, ∃₀ t ∈ F₂, r ⊇ s ∩ t},
  univ_mem_sets := abstract
                     bounded_exists.intro (univ_mem_sets F₁)
                       (bounded_exists.intro (univ_mem_sets F₂)
                         (by rewrite univ_inter; apply subset.refl))
                   end,
  inter_closed  := abstract
                     λ a b Ha Hb,
                     obtain a₁ [a₁F₁ [a₂ [a₂F₂ (Ha' : a ⊇ a₁ ∩ a₂)]]], from Ha,
                     obtain b₁ [b₁F₁ [b₂ [b₂F₂ (Hb' : b ⊇ b₁ ∩ b₂)]]], from Hb,
                     assert a₁ ∩ b₁ ∩ (a₂ ∩ b₂) = a₁ ∩ a₂ ∩ (b₁ ∩ b₂),
                       by rewrite [*inter.assoc, inter.left_comm b₁],
                     have a ∩ b ⊇ a₁ ∩ b₁ ∩ (a₂ ∩ b₂),
                       begin
                         rewrite this,
                         apply subset_inter,
                           {apply subset.trans,
                             apply inter_subset_left,
                             exact Ha'},
                         apply subset.trans,
                         apply inter_subset_right,
                         exact Hb'
                       end,
                     bounded_exists.intro (inter_closed F₁ a₁F₁ b₁F₁)
                       (bounded_exists.intro (inter_closed F₂ a₂F₂ b₂F₂)
                                                this)
                   end,
  is_mono       := abstract
                     λ a b Hsub Ha,
                     obtain a₁ [a₁F₁ [a₂ [a₂F₂ (Ha' : a ⊇ a₁ ∩ a₂)]]], from Ha,
                     bounded_exists.intro a₁F₁
                       (bounded_exists.intro a₂F₂ (subset.trans Ha' Hsub))
                   end
⦄
infix `⊓`:70 := inf

definition Sup (S : set (filter A)) : filter A :=
⦃ filter,
  sets          := {s | ∀₀ F ∈ S, s ∈ F},
  univ_mem_sets := λ F FS, univ_mem_sets F,
  inter_closed  := abstract
                     λ a b Ha Hb F FS,
                       inter_closed F (Ha F FS) (Hb F FS)
                   end,
  is_mono       := abstract
                     λ a b asubb Ha F FS,
                       is_mono F asubb (Ha F FS)
                   end
⦄
prefix `⨆`:65 := Sup

definition Inf (S : set (filter A)) : filter A :=
Sup {F | ∀ G, G ∈ S → G ≽ F}

prefix `⨅`:70 := Inf

theorem eventually_of_refines (H₁ : eventually P F₁) (H₂ : F₁ ≽ F₂) : eventually P F₂ := H₂ H₁

theorem refines_of_forall (H : ∀ P, eventually P F₁ → eventually P F₂) : F₁ ≽ F₂ := H

theorem eventually_bot (P : A → Prop) : eventually P ⊥ := trivial

theorem refines_bot (F : filter A) : F ≽ ⊥ :=
take P, suppose eventually P F, eventually_bot P

theorem eventually_top_of_forall (H : ∀ x, P x) : eventually P ⊤ :=
by rewrite [↑eventually, ↑top, mem_singleton_iff]; exact eq_univ_of_forall H

theorem forall_of_eventually_top : eventually P ⊤ → ∀ x, P x :=
by rewrite [↑eventually, ↑top, mem_singleton_iff]; intro H x; rewrite H; exact trivial

theorem eventually_top (P : A → Prop) : eventually P top ↔ ∀ x, P x :=
iff.intro forall_of_eventually_top eventually_top_of_forall

theorem top_refines (F : filter A) : ⊤ ≽ F :=
take P, suppose eventually P top,
eventually_of_forall F (forall_of_eventually_top this)

theorem eventually_sup (P : A → Prop) (F₁ F₂ : filter A) :
  eventually P (sup F₁ F₂) ↔ eventually P F₁ ∧ eventually P F₂ :=
!iff.refl

theorem sup_refines_left (F₁ F₂ : filter A) : F₁ ⊔ F₂ ≽ F₁ :=
inter_subset_left _ _

theorem sup_refines_right (F₁ F₂ : filter A) : F₁ ⊔ F₂ ≽ F₂ :=
inter_subset_right _ _

theorem refines_sup (H₁ : F ≽ F₁) (H₂ : F ≽ F₂) : F ≽ F₁ ⊔ F₂ :=
subset_inter H₁ H₂

theorem refines_inf_left (F₁ F₂ : filter A) : F₁ ≽ F₁ ⊓ F₂ :=
take s, suppose s ∈ F₁,
  bounded_exists.intro `s ∈ F₁`
    (bounded_exists.intro (univ_mem_sets F₂) (by rewrite inter_univ; apply subset.refl))

theorem refines_inf_right (F₁ F₂ : filter A) : F₂ ≽ F₁ ⊓ F₂ :=
take s, suppose s ∈ F₂,
  bounded_exists.intro (univ_mem_sets F₁)
    (bounded_exists.intro `s ∈ F₂` (by rewrite univ_inter; apply subset.refl))

theorem inf_refines (H₁ : F₁ ≽ F) (H₂ : F₂ ≽ F) : F₁ ⊓ F₂ ≽ F :=
take s, suppose s ∈ F₁ ⊓ F₂,
  obtain a₁ [a₁F₁ [a₂ [a₂F₂ (Hsub : s ⊇ a₁ ∩ a₂)]]], from this,
  have a₁ ∈ F, from H₁ a₁F₁,
  have a₂ ∈ F, from H₂ a₂F₂,
  show s ∈ F, from is_mono F Hsub (inter_closed F `a₁ ∈ F` `a₂ ∈ F`)

theorem refines_Sup {F : filter A} {S : set (filter A)} (H : ∀₀ G ∈ S, F ≽ G) : F ≽ ⨆ S :=
λ s Fs G GS, H GS Fs

theorem Sup_refines {F : filter A} {S : set (filter A)} (FS : F ∈ S) : ⨆ S ≽ F :=
λ s sInfS, sInfS F FS

theorem Inf_refines {F : filter A} {S : set (filter A)} (H : ∀₀ G ∈ S, G ≽ F) : ⨅ S ≽ F :=
Sup_refines H

theorem refines_Inf {F : filter A} {S : set (filter A)} (FS : F ∈ S) : F ≽ ⨅ S :=
refines_Sup (λ G GS, GS F FS)

open algebra
protected definition complete_lattice_Inf [reducible] [instance] : complete_lattice_Inf (filter A) :=
⦃ algebra.complete_lattice_Inf,
  le           := weakens,
  le_refl      := weakens.refl,
  le_trans     := @weakens.trans A,
  le_antisymm  := @weakens.antisymm A,
--  inf          := inf,
--  le_inf       := @inf_refines A,
--  inf_le_left  := refines_inf_left,
--  inf_le_right := refines_inf_right,
--  sup          := sup,
--  sup_le       := @refines_sup A,
--  le_sup_left  := sup_refines_left,
--  le_sup_right := sup_refines_right,
  Inf          := Inf,
  Inf_le       := @refines_Inf A,
  le_Inf       := @Inf_refines A
⦄

-- The previous instance is enough for showing that (filter A) is a complete_lattice
example {A : Type} : complete_lattice (filter A) :=
_

end filter
end set
