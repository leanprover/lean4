/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Jacob Gross

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

theorem eventually_of_eventually_and_left {P Q : A → Prop} {F : filter A}
    (H : eventually (λ x, P x ∧ Q x) F) :
  eventually P F :=
!filter.is_mono (λ x HPQ, and.elim_left HPQ) H

theorem eventually_of_eventually_and_right {P Q : A → Prop} {F : filter A}
    (H : eventually (λ x, P x ∧ Q x) F) :
  eventually Q F :=
!filter.is_mono (λ x HPQ, and.elim_right HPQ) H

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

/- filters form a lattice under ⊇ -/

protected theorem eq : sets F₁ = sets F₂ → F₁ = F₂ :=
begin
  cases F₁ with s₁ u₁ i₁ m₁, cases F₂ with s₂ u₂ i₂ m₂, esimp,
  intro eqs₁s₂, revert [u₁, i₁, m₁, u₂, i₂, m₂],
  subst s₁, intros, exact rfl
end

namespace complete_lattice
  definition le [reducible] (F₁ F₂ : filter A) := F₁ ⊇ F₂
  local infix `≤`:50 := le

  definition ge [reducible] (F₁ F₂ : filter A) := F₁ ⊆ F₂
  local infix `≥`:50 := ge

  theorem le_refl (F : filter A) : F ≤ F := subset.refl _

  theorem le_trans {F₁ F₂ F₃ : filter A} (H₁ : F₁ ≤ F₂) (H₂ : F₂ ≤ F₃) : F₁ ≤ F₃ :=
  subset.trans H₂ H₁

  theorem le_antisymm (H₁ : F₁ ≤ F₂) (H₂ : F₂ ≤ F₁) : F₁ = F₂ :=
  filter.eq (eq_of_subset_of_subset H₂ H₁)

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
  local infix ` ⊔ `:65 := sup

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
                         by rewrite [*inter_assoc, inter_left_comm b₁],
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
    sets          := ⋂ F ∈ S, sets F,
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
  local prefix `⨆ `:65 := Sup

  definition Inf (S : set (filter A)) : filter A :=
  Sup {F | ∀ G, G ∈ S → G ≥ F}

  local prefix `⨅ `:70 := Inf

  theorem le_sup_left (F₁ F₂ : filter A) : F₁ ≤ F₁ ⊔ F₂ :=
  inter_subset_left _ _

  theorem le_sup_right (F₁ F₂ : filter A) : F₂ ≤ F₁ ⊔ F₂ :=
  inter_subset_right _ _

  theorem sup_le (H₁ : F₁ ≤ F) (H₂ : F₂ ≤ F) : F₁ ⊔ F₂ ≤ F :=
  subset_inter H₁ H₂

  theorem inf_le_left (F₁ F₂ : filter A) : F₁ ⊓ F₂ ≤ F₁ :=
  take s, suppose s ∈ F₁,
    bounded_exists.intro `s ∈ F₁`
      (bounded_exists.intro (univ_mem_sets F₂) (by rewrite inter_univ; apply subset.refl))

  theorem inf_le_right (F₁ F₂ : filter A) : F₁ ⊓ F₂ ≤ F₂ :=
  take s, suppose s ∈ F₂,
    bounded_exists.intro (univ_mem_sets F₁)
      (bounded_exists.intro `s ∈ F₂` (by rewrite univ_inter; apply subset.refl))

  theorem le_inf (H₁ : F ≤ F₁) (H₂ : F ≤ F₂) : F ≤ F₁ ⊓ F₂ :=
  take s : set A, suppose (s ∈ (F₁ ⊓ F₂ : set (set A))),
  obtain a₁ [a₁F₁ [a₂ [a₂F₂ (Hsub : s ⊇ a₁ ∩ a₂)]]], from this,
  have a₁ ∈ F, from H₁ a₁F₁,
  have a₂ ∈ F, from H₂ a₂F₂,
  show s ∈ F, from is_mono F Hsub (inter_closed F `a₁ ∈ F` `a₂ ∈ F`)

  theorem Sup_le {F : filter A} {S : set (filter A)} (H : ∀₀ G ∈ S, G ≤ F) : ⨆ S ≤ F :=
  λ s Fs G GS, H GS Fs

  theorem le_Sup {F : filter A} {S : set (filter A)} (FS : F ∈ S) : F ≤ ⨆ S :=
  λ s sInfS, sInfS F FS

  theorem le_Inf {F : filter A} {S : set (filter A)} (H : ∀₀ G ∈ S, F ≤ G) : F ≤ ⨅ S :=
  le_Sup H

  theorem Inf_le {F : filter A} {S : set (filter A)} (FS : F ∈ S) : ⨅ S ≤ F :=
  Sup_le (λ G GS, GS F FS)
end complete_lattice

protected definition complete_lattice [reducible] [trans_instance] : complete_lattice (filter A) :=
⦃ complete_lattice,
  le           := complete_lattice.le,
  le_refl      := complete_lattice.le_refl,
  le_trans     := @complete_lattice.le_trans A,
  le_antisymm  := @complete_lattice.le_antisymm A,
  inf          := complete_lattice.inf,
  le_inf       := @complete_lattice.le_inf A,
  inf_le_left  := @complete_lattice.inf_le_left A,
  inf_le_right := @complete_lattice.inf_le_right A,
  sup          := complete_lattice.sup,
  sup_le       := @complete_lattice.sup_le A,
  le_sup_left  := complete_lattice.le_sup_left,
  le_sup_right := complete_lattice.le_sup_right,
  Inf          := complete_lattice.Inf,
  Inf_le       := @complete_lattice.Inf_le A,
  le_Inf       := @complete_lattice.le_Inf A,
  Sup          := complete_lattice.Sup,
  Sup_le       := @complete_lattice.Sup_le A,
  le_Sup       := @complete_lattice.le_Sup A
⦄

protected theorem le_of_subset {F₁ F₂ : filter A} (H : F₁ ≤ F₂) : sets F₂ ⊆ sets F₁ := H

protected theorem subset_of_le {F₁ F₂ : filter A} (H : sets F₂ ⊆ sets F₁) : F₁ ≤ F₂ := H

theorem sets_Sup (S : set (filter A)) : sets (⨆ S) = ⋂ F ∈ S, sets F := rfl

theorem sets_sup (F₁ F₂ : filter A) : sets (F₁ ⊔ F₂) = sets F₁ ∩ sets F₂ := rfl

theorem sets_inf (F₁ F₂ : filter A) : sets (F₁ ⊓ F₂) = {r | ∃₀ s ∈ F₁, ∃₀ t ∈ F₂, r ⊇ s ∩ t} := rfl

/- eventually and lattice operations -/

theorem eventually_of_le (H₁ : eventually P F₁) (H₂ : F₂ ≤ F₁) : eventually P F₂ :=
filter.subset_of_le H₂ H₁

theorem le_of_forall_eventually (H : ∀ P, eventually P F₁ → eventually P F₂) : F₂ ≤ F₁ := H

theorem eventually_Sup_iff (P : A → Prop) (S : set (filter A)) :
  eventually P (⨆ S) ↔ ∀₀ F ∈ S, eventually P F :=
by rewrite [↑eventually, sets_Sup]

theorem eventually_Sup {P : A → Prop} {S : set (filter A)} (H : ∀₀ F ∈ S, eventually P F) :
  eventually P (⨆ S) :=
iff.mpr (eventually_Sup_iff P S) H

theorem eventually_of_eventually_Sup {P : A → Prop} {S : set (filter A)}
    (H : eventually P (⨆ S)) {F : filter A} (FS : F ∈ S) :
  eventually P F :=
iff.mp (eventually_Sup_iff P S) H F FS

theorem eventually_sup_iff (P : A → Prop) (F₁ F₂ : filter A) :
  eventually P (F₁ ⊔ F₂) ↔ eventually P F₁ ∧ eventually P F₂ :=
by rewrite [↑eventually, sets_sup]

theorem eventually_sup {P : A → Prop} {F₁ F₂ : filter A}
    (H₁ : eventually P F₁) (H₂ : eventually P F₂) :
  eventually P (F₁ ⊔ F₂) :=
iff.mpr (eventually_sup_iff P F₁ F₂) (and.intro H₁ H₂)

theorem eventually_of_eventually_sup_left {P : A → Prop} {F₁ F₂ : filter A}
    (H : eventually P (F₁ ⊔ F₂)) : eventually P F₁ :=
and.left (iff.mp (eventually_sup_iff P F₁ F₂) H)

theorem eventually_of_eventually_sup_right {P : A → Prop} {F₁ F₂ : filter A}
    (H : eventually P (F₁ ⊔ F₂)) : eventually P F₂ :=
and.right (iff.mp (eventually_sup_iff P F₁ F₂) H)

theorem eventually_inf_iff (P : A → Prop) (F₁ F₂ : filter A) :
  eventually P (F₁ ⊓ F₂) ↔ (∃ S, eventually S F₁ ∧ ∃ T, eventually T F₂ ∧ (P ⊇ S ∩ T)) :=
by rewrite [↑eventually, sets_inf]

theorem eventually_inf {P : A → Prop} {F₁ F₂ : filter A}
   {S : A → Prop} (HS : eventually S F₁) (T : A → Prop) (HT : eventually T F₂) (HP : P ⊇ S ∩ T) :
  eventually P (F₁ ⊓ F₂) :=
iff.mpr (eventually_inf_iff P F₁ F₂)
  (exists.intro S (and.intro HS (exists.intro T (and.intro HT HP))))

theorem exists_of_eventually_inf {P : A → Prop} {F₁ F₂ : filter A} (H : eventually P (F₁ ⊓ F₂)) :
  ∃ S, eventually S F₁ ∧ ∃ T, eventually T F₂ ∧ (P ⊇ S ∩ T) :=
iff.mp (eventually_inf_iff P F₁ F₂) H

/- top and bot -/

protected definition bot (A : Type) : filter A :=
⦃ filter,
  sets           := univ,
  univ_mem_sets  := trivial,
  inter_closed := λ a b Ha Hb, trivial,
  is_mono        := λ a b Ha Hsub, trivial
⦄

protected definition top (A : Type) : filter A :=
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

protected theorem bot_eq : ⊥ = filter.bot A :=
le.antisymm !bot_le
  begin
    apply le_of_forall_eventually,
    intro P H,
    apply mem_univ
  end

protected theorem top_eq : ⊤ = filter.top A :=
le.antisymm
  (le_of_forall_eventually
    (λ P H,
      have P = univ, from eq_of_mem_singleton H,
      by+ rewrite this; apply eventually_true ⊤))
  !le_top

theorem sets_bot_eq : sets ⊥ = (univ : set (set A)) :=
by rewrite filter.bot_eq

theorem sets_top_eq : sets ⊤ = ('{univ} : set (set A)) :=
by rewrite filter.top_eq

theorem eventually_bot (P : A → Prop) : eventually P ⊥ :=
by rewrite [↑eventually, sets_bot_eq]; apply mem_univ

theorem eventually_top_of_forall (H : ∀ x, P x) : eventually P ⊤ :=
by rewrite [↑eventually, sets_top_eq, mem_singleton_iff]; exact eq_univ_of_forall H

theorem forall_of_eventually_top : eventually P ⊤ → ∀ x, P x :=
by rewrite [↑eventually, sets_top_eq, mem_singleton_iff]; intro H x; rewrite H; exact trivial

theorem eventually_top_iff (P : A → Prop) : eventually P top ↔ ∀ x, P x :=
iff.intro forall_of_eventually_top eventually_top_of_forall

end filter
end set
