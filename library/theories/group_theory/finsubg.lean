/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/

-- develop the concept of finite subgroups based on finsets so that the properties
-- can be used directly without translating from the set based theory first

import data algebra.group .subgroup
open function algebra finset
-- ⁻¹ in eq.ops conflicts with group ⁻¹
open eq.ops

namespace group
open ops

section subg
-- we should be able to prove properties using finsets directly
variable {G : Type}
variable [ambientG : group G]
include ambientG

definition finset_mul_closed_on [reducible] (H : finset G) : Prop :=
           ∀ x y : G, x ∈ H → y ∈ H → x * y ∈ H
definition finset_has_inv (H : finset G) : Prop :=
           ∀ a : G, a ∈ H → a⁻¹ ∈ H

structure is_finsubg [class] (H : finset G) : Type :=
          (has_one : 1 ∈ H)
          (mul_closed : finset_mul_closed_on H)
          (has_inv : finset_has_inv H)

definition univ_is_finsubg [instance] [finG : fintype G] : is_finsubg (@finset.univ G _) :=
is_finsubg.mk !mem_univ (λ x y Px Py, !mem_univ) (λ a Pa, !mem_univ)

definition one_is_finsubg [instance] : is_finsubg (singleton (1:G)) :=
is_finsubg.mk !mem_singleton
  (λ x y Px Py, by rewrite [eq_of_mem_singleton Px, eq_of_mem_singleton Py, one_mul]; apply mem_singleton)
  (λ x Px, by rewrite [eq_of_mem_singleton Px, one_inv]; apply mem_singleton)

lemma finsubg_has_one (H : finset G) [h : is_finsubg H] : 1 ∈ H :=
      @is_finsubg.has_one G _ H h
lemma finsubg_mul_closed (H : finset G) [h : is_finsubg H] {x y : G} : x ∈ H → y ∈ H → x * y ∈ H :=
      @is_finsubg.mul_closed G _ H h x y
lemma finsubg_has_inv (H : finset G) [h : is_finsubg H] {a : G} :  a ∈ H → a⁻¹ ∈ H :=
      @is_finsubg.has_inv G _ H h a

variable [deceqG : decidable_eq G]
include deceqG

definition finsubg_to_subg [instance] {H : finset G} [h : is_finsubg H]
         : is_subgroup (ts H) :=
           is_subgroup.mk
           (mem_eq_mem_to_set H 1 ▸ finsubg_has_one H)
           (take x y, begin repeat rewrite -mem_eq_mem_to_set,
             apply finsubg_mul_closed H end)
           (take a, begin repeat rewrite -mem_eq_mem_to_set,
             apply finsubg_has_inv H end)

open nat
lemma finsubg_eq_singleton_one_of_card_one {H : finset G} [h : is_finsubg H] :
  card H = 1 → H = singleton 1 :=
assume Pcard, eq.symm (eq_of_card_eq_of_subset (by rewrite [Pcard])
  (subset_of_forall take g,
    by rewrite [mem_singleton_eq]; intro Pg; rewrite Pg; exact finsubg_has_one H))

end subg

section fin_lcoset

open set

variable {A : Type}
variable [deceq : decidable_eq A]
include deceq
variable [s : group A]
include s

definition fin_lcoset (H : finset A) (a : A) := finset.image (lmul_by a) H

definition fin_rcoset (H : finset A) (a : A) : finset A := image (rmul_by a) H

definition fin_lcosets (H G : finset A) := image (fin_lcoset H) G

definition fin_inv : finset A → finset A := image has_inv.inv

variable {H : finset A}

lemma lmul_rmul {a b : A} : (lmul_by a) ∘ (rmul_by b) = (rmul_by b) ∘ (lmul_by a) :=
funext take c, calc a*(c*b) = (a*c)*b : mul.assoc

lemma fin_lrcoset_comm {a b : A} :
  fin_lcoset (fin_rcoset H b) a = fin_rcoset (fin_lcoset H a) b :=
by esimp [fin_lcoset, fin_rcoset]; rewrite [-*image_compose, lmul_rmul]

lemma inv_mem_fin_inv {a : A} : a ∈ H → a⁻¹ ∈ fin_inv H :=
assume Pin, mem_image Pin rfl

lemma fin_lcoset_eq (a : A) : ts (fin_lcoset H a) = a ∘> (ts H) := calc
      ts (fin_lcoset H a) = coset.l a (ts H) : to_set_image
      ... = a ∘> (ts H) : glcoset_eq_lcoset

lemma fin_lcoset_id : fin_lcoset H 1 = H :=
by rewrite [eq_eq_to_set_eq, fin_lcoset_eq, glcoset_id]

lemma fin_lcoset_compose (a b : A) : fin_lcoset (fin_lcoset H b) a = fin_lcoset H (a*b) :=
to_set.inj (by rewrite [*fin_lcoset_eq, glcoset_compose])

lemma fin_lcoset_inv (a : A) : fin_lcoset (fin_lcoset H a) a⁻¹ = H :=
to_set.inj (by rewrite [*fin_lcoset_eq, glcoset_inv])

lemma fin_lcoset_card (a : A) : card (fin_lcoset H a) = card H :=
      card_image_eq_of_inj_on (lmul_inj_on a (ts H))
lemma fin_lcosets_card_eq {G : finset A} : ∀ gH, gH ∈ fin_lcosets H G → card gH = card H :=
      take gH, assume Pcosets, obtain g Pg, from exists_of_mem_image Pcosets,
      and.right Pg ▸ fin_lcoset_card g

variable [is_finsubgH : is_finsubg H]
include is_finsubgH

lemma fin_lcoset_same (x a : A) : x ∈ (fin_lcoset H a) = (fin_lcoset H x = fin_lcoset H a) :=
      begin
        rewrite mem_eq_mem_to_set,
        rewrite [eq_eq_to_set_eq, *(fin_lcoset_eq x), fin_lcoset_eq a],
        exact (subg_lcoset_same x a)
      end
lemma fin_mem_lcoset (g : A) : g ∈ fin_lcoset H g :=
      have P : g ∈ g ∘> ts H, from and.left (subg_in_coset_refl g),
      assert P1 : g ∈ ts (fin_lcoset H g), from eq.symm (fin_lcoset_eq g) ▸ P,
      eq.symm (mem_eq_mem_to_set _ g) ▸ P1
lemma fin_lcoset_subset {S : finset A} (Psub : S ⊆ H) : ∀ x, x ∈ H → fin_lcoset S x ⊆ H :=
      assert Psubs : set.subset (ts S) (ts H), from subset_eq_to_set_subset S H ▸ Psub,
      take x, assume Pxs : x ∈ ts H,
      assert Pcoset : set.subset (x ∘> ts S) (ts H), from subg_lcoset_subset_subg Psubs x Pxs,
      by rewrite [subset_eq_to_set_subset, fin_lcoset_eq x]; exact Pcoset

lemma finsubg_lcoset_id {a : A} : a ∈ H → fin_lcoset H a = H :=
by rewrite [eq_eq_to_set_eq, fin_lcoset_eq, mem_eq_mem_to_set]; apply subgroup_lcoset_id

lemma finsubg_inv_lcoset_eq_rcoset {a : A} :
  fin_inv (fin_lcoset H a) = fin_rcoset H a⁻¹ :=
begin
  esimp [fin_inv, fin_lcoset, fin_rcoset],
  rewrite [-image_compose],
  apply ext, intro b,
  rewrite [*mem_image_iff, ↑compose, ↑lmul_by, ↑rmul_by],
  apply iff.intro,
    intro Pl, cases Pl with h Ph, cases Ph with Pin Peq,
    existsi h⁻¹, apply and.intro,
      exact finsubg_has_inv H Pin,
      rewrite [-mul_inv, Peq],
    intro Pr, cases Pr with h Ph, cases Ph with Pin Peq,
    existsi h⁻¹, apply and.intro,
      exact finsubg_has_inv H Pin,
      rewrite [mul_inv, inv_inv, Peq],
end

lemma finsubg_conj_closed {g h : A} : g ∈ H → h ∈ H → g ∘c h ∈ H :=
assume Pgin Phin, finsubg_mul_closed H (finsubg_mul_closed H Pgin Phin) (finsubg_has_inv H Pgin)

variable {G : finset A}
variable [is_finsubgG : is_finsubg G]
include is_finsubgG

open finset.partition

definition fin_lcoset_partition_subg (Psub : H ⊆ G) :=
      partition.mk G (fin_lcoset H) fin_lcoset_same
        (restriction_imp_union (fin_lcoset H) fin_lcoset_same (fin_lcoset_subset Psub))

open nat

theorem lagrange_theorem (Psub : H ⊆ G) : card G = card (fin_lcosets H G) * card H := calc
        card G = nat.Sum (fin_lcosets H G) card : class_equation (fin_lcoset_partition_subg Psub)
        ... = nat.Sum (fin_lcosets H G) (λ x, card H) : nat.Sum_ext (take g P, fin_lcosets_card_eq g P)
        ... = card (fin_lcosets H G) * card H : Sum_const_eq_card_mul

end fin_lcoset

section
open fintype list subtype

lemma dinj_tag {A : Type} (P : A → Prop) : dinj P tag :=
take a₁ a₂ Pa₁ Pa₂ Pteq, subtype.no_confusion Pteq (λ Pe Pqe, Pe)

open nat

lemma card_pos {A : Type} [ambientA : group A] [finA : fintype A] : 0 < card A :=
  length_pos_of_mem (mem_univ 1)

end

section lcoset_fintype
open fintype list subtype

variables {A : Type} [ambientA : group A] [finA : fintype A] [deceqA : decidable_eq A]
include ambientA deceqA finA

variables G H : finset A

definition is_fin_lcoset [reducible] (S : finset A) : Prop :=
  ∃ g, g ∈ G ∧ fin_lcoset H g = S

definition to_list : list A := list.filter (λ g, g ∈ G) (elems A)

definition list_lcosets : list (finset A) := erase_dup (map (fin_lcoset H) (to_list G))

definition lcoset_type [reducible] : Type := {S : finset A | is_fin_lcoset G H S}

definition all_lcosets : list (lcoset_type G H) :=
dmap (is_fin_lcoset G H) tag (list_lcosets G H)

variables {G H} [finsubgG : is_finsubg G]

include finsubgG

lemma self_is_lcoset : is_fin_lcoset G H H :=
exists.intro 1 (and.intro !finsubg_has_one fin_lcoset_id)

lemma lcoset_subset_of_subset (J : lcoset_type G H) : H ⊆ G → elt_of J ⊆ G :=
assume Psub, obtain j Pjin Pj, from has_property J,
by rewrite [-Pj]; apply fin_lcoset_subset Psub; exact Pjin

variables (G H)

definition lcoset_one : lcoset_type G H := tag H self_is_lcoset

variables {G H}

definition lcoset_lmul {g : A} (Pgin : g ∈ G) (S : lcoset_type G H)
  : lcoset_type G H :=
tag (fin_lcoset (elt_of S) g)
  (obtain f Pfin Pf, from has_property S,
  exists.intro (g*f)
    (by apply and.intro;
      exact finsubg_mul_closed G Pgin Pfin;
      rewrite [-Pf, -fin_lcoset_compose]))

definition lcoset_mul (S₁ S₂ : lcoset_type G H): finset A :=
Union (elt_of S₁) (fin_lcoset (elt_of S₂))

lemma mul_mem_lcoset_mul (J K : lcoset_type G H) {g h} :
  g ∈ elt_of J → h ∈ elt_of K → g*h ∈ lcoset_mul J K :=
assume Pg, begin
  rewrite [↑lcoset_mul, mem_Union_iff, ↑fin_lcoset],
  intro Ph, existsi g, apply and.intro, exact Pg,
  rewrite [mem_image_iff, ↑lmul_by],
  existsi h, exact and.intro Ph rfl
end

lemma is_lcoset_of_mem_list_lcosets {S : finset A}
  : S ∈ list_lcosets G H → is_fin_lcoset G H S :=
assume Pin, obtain g Pgin Pg, from exists_of_mem_map (mem_of_mem_erase_dup Pin),
exists.intro g (and.intro (of_mem_filter Pgin) Pg)

lemma mem_list_lcosets_of_is_lcoset {S : finset A}
  : is_fin_lcoset G H S → S ∈ list_lcosets G H :=
assume Plcoset, obtain g Pgin Pg, from Plcoset,
Pg ▸ mem_erase_dup (mem_map _ (mem_filter_of_mem (complete g) Pgin))

lemma fin_lcosets_eq :
  fin_lcosets H G = to_finset_of_nodup (list_lcosets G H) !nodup_erase_dup :=
ext (take S, iff.intro
  (λ Pimg, mem_list_lcosets_of_is_lcoset (exists_of_mem_image Pimg))
  (λ Pl, obtain g Pg, from is_lcoset_of_mem_list_lcosets Pl,
    iff.elim_right !mem_image_iff (is_lcoset_of_mem_list_lcosets Pl)))

lemma length_all_lcosets : length (all_lcosets G H) = card (fin_lcosets H G) :=
eq.trans
  (show length (all_lcosets G H) = length (list_lcosets G H), from
    assert Pmap : map elt_of (all_lcosets G H) = list_lcosets G H, from
      map_dmap_of_inv_of_pos (λ S P, rfl) (λ S, is_lcoset_of_mem_list_lcosets),
    by rewrite[-Pmap, length_map])
  (by rewrite fin_lcosets_eq)

lemma lcoset_lmul_compose {f g : A} (Pf : f ∈ G) (Pg : g ∈ G) (S : lcoset_type G H) :
lcoset_lmul Pf (lcoset_lmul Pg S) = lcoset_lmul (finsubg_mul_closed G Pf Pg) S :=
subtype.eq !fin_lcoset_compose

lemma lcoset_lmul_one (S : lcoset_type G H) : lcoset_lmul !finsubg_has_one S = S :=
subtype.eq fin_lcoset_id

lemma lcoset_lmul_inv {g : A} {Pg : g ∈ G} (S : lcoset_type G H) :
  lcoset_lmul (finsubg_has_inv G Pg) (lcoset_lmul Pg S) = S :=
subtype.eq (to_set.inj begin
 esimp [lcoset_lmul],
 rewrite [fin_lcoset_compose, mul.left_inv, fin_lcoset_eq, glcoset_id]
end)

lemma lcoset_lmul_inj {g : A} {Pg : g ∈ G}:
  @injective (lcoset_type G H) _ (lcoset_lmul Pg) :=
injective_of_has_left_inverse (exists.intro (lcoset_lmul (finsubg_has_inv G Pg)) lcoset_lmul_inv)

lemma card_elt_of_lcoset_type (S : lcoset_type G H) : card (elt_of S) = card H :=
obtain f Pfin Pf, from has_property S, Pf ▸ fin_lcoset_card f

definition lcoset_fintype [instance] : fintype (lcoset_type G H) :=
fintype.mk (all_lcosets G H)
  (dmap_nodup_of_dinj (dinj_tag (is_fin_lcoset G H)) !nodup_erase_dup)
  (take s, subtype.destruct s (take S, assume PS, mem_dmap PS (mem_list_lcosets_of_is_lcoset PS)))

lemma card_lcoset_type : card (lcoset_type G H) = card (fin_lcosets H G) :=
length_all_lcosets

open nat
variable [finsubgH : is_finsubg H]
include finsubgH

theorem lagrange_theorem' (Psub : H ⊆ G) : card G = card (lcoset_type G H) * card H :=
calc card G = card (fin_lcosets H G) * card H : lagrange_theorem Psub
        ... = card (lcoset_type G H) * card H : card_lcoset_type

lemma lcoset_disjoint {S₁ S₂ : lcoset_type G H} : S₁ ≠ S₂ → elt_of S₁ ∩ elt_of S₂ = ∅ :=
obtain f₁ Pfin₁ Pf₁, from has_property S₁,
obtain f₂ Pfin₂ Pf₂, from has_property S₂,
assume Pne, inter_eq_empty_of_disjoint (disjoint.intro
  take g, begin
  rewrite [-Pf₁, -Pf₂, *fin_lcoset_same],
  intro Pgf₁, rewrite [Pgf₁, Pf₁, Pf₂],
  intro Peq, exact absurd (subtype.eq Peq) Pne
  end )

lemma card_Union_lcosets (lcs : finset (lcoset_type G H)) :
  card (Union lcs elt_of) = card lcs * card H :=
calc card (Union lcs elt_of) = ∑ lc ∈ lcs, card (elt_of lc) : card_Union_of_disjoint lcs elt_of (λ (S₁ S₂ : lcoset_type G H) P₁ P₂ Pne, lcoset_disjoint Pne)
                         ... = ∑ lc ∈ lcs, card H : Sum_ext (take lc P, card_elt_of_lcoset_type _)
                         ... = card lcs * card H : Sum_const_eq_card_mul

lemma exists_of_lcoset_type (J : lcoset_type G H) :
  ∃ j, j ∈ elt_of J ∧ fin_lcoset H j = elt_of J :=
obtain j Pjin Pj, from has_property J,
exists.intro j (and.intro (Pj ▸ !fin_mem_lcoset) Pj)

lemma lcoset_not_empty (J : lcoset_type G H) : elt_of J ≠ ∅ :=
obtain j Pjin Pj, from has_property J,
assume Pempty, absurd (by rewrite [-Pempty, -Pj]; apply fin_mem_lcoset) (not_mem_empty j)

end lcoset_fintype

section normalizer
open subtype

variables {G : Type} [ambientG : group G] [finG : fintype G] [deceqG : decidable_eq G]
include ambientG deceqG finG

variable H : finset G

definition normalizer : finset G := {g ∈ univ | ∀ h, h ∈ H → g ∘c h ∈ H}

variable {H}

variable [finsubgH : is_finsubg H]
include finsubgH

lemma subset_normalizer : H ⊆ normalizer H :=
subset_of_forall take g, assume PginH, mem_filter_of_mem !mem_univ
  (take h, assume PhinH, finsubg_conj_closed PginH PhinH)

lemma normalizer_has_one : 1 ∈ normalizer H :=
mem_of_subset_of_mem subset_normalizer (finsubg_has_one H)

lemma normalizer_mul_closed : finset_mul_closed_on (normalizer H) :=
take f g, assume Pfin Pgin,
mem_filter_of_mem !mem_univ take h, assume Phin, begin
  rewrite [-conj_compose],
  apply of_mem_filter Pfin,
  apply of_mem_filter Pgin,
  exact Phin
end

lemma conj_eq_of_mem_normalizer {g : G} : g ∈ normalizer H → image (conj_by g) H = H :=
assume Pgin,
eq_of_card_eq_of_subset (card_image_eq_of_inj_on (take h j, assume P1 P2, !conj_inj))
  (subset_of_forall take h, assume Phin,
  obtain j Pjin Pj, from exists_of_mem_image Phin,
  begin substvars, apply of_mem_filter Pgin, exact Pjin end)

lemma normalizer_has_inv : finset_has_inv (normalizer H) :=
take g, assume Pgin,
mem_filter_of_mem !mem_univ take h, begin
  rewrite [-(conj_eq_of_mem_normalizer Pgin) at {1}, mem_image_iff],
  intro Pex, cases Pex with k Pk,
  rewrite [-(and.right Pk), conj_compose, mul.left_inv, conj_id],
  exact and.left Pk
end

definition normalizer_is_finsubg [instance] : is_finsubg (normalizer H) :=
is_finsubg.mk normalizer_has_one normalizer_mul_closed normalizer_has_inv

lemma lcoset_subset_normalizer (J : lcoset_type (normalizer H) H) :
  elt_of J ⊆ normalizer H :=
lcoset_subset_of_subset J subset_normalizer

lemma lcoset_subset_normalizer_of_mem {g : G} :
  g ∈ normalizer H → fin_lcoset H g ⊆ normalizer H :=
assume Pgin, fin_lcoset_subset subset_normalizer g Pgin

lemma lrcoset_same_of_mem_normalizer {g : G} :
  g ∈ normalizer H → fin_lcoset H g = fin_rcoset H g :=
assume Pg, ext take h, iff.intro
  (assume Pl, obtain j Pjin Pj, from exists_of_mem_image Pl,
  mem_image (of_mem_filter Pg j Pjin)
    (calc g*j*g⁻¹*g = g*j : inv_mul_cancel_right
                ... = h   : Pj))
  (assume Pr, obtain j Pjin Pj, from exists_of_mem_image Pr,
  mem_image (of_mem_filter (finsubg_has_inv (normalizer H) Pg) j Pjin)
    (calc g*(g⁻¹*j*g⁻¹⁻¹) = g*(g⁻¹*j*g)   : inv_inv
                      ... = g*(g⁻¹*(j*g)) : mul.assoc
                      ... = j*g           : mul_inv_cancel_left
                      ... = h             : Pj))

lemma lcoset_mul_eq_lcoset (J K : lcoset_type (normalizer H) H) {g : G} :
  g ∈ elt_of J → (lcoset_mul J K) = fin_lcoset (elt_of K) g :=
assume Pgin,
obtain j Pjin Pj, from has_property J,
obtain k Pkin Pk, from has_property K,
Union_const (lcoset_not_empty J) begin
  rewrite [-Pk], intro h Phin,
  assert Phinn : h ∈ normalizer H,
    apply mem_of_subset_of_mem (lcoset_subset_normalizer_of_mem Pjin),
    rewrite Pj, assumption,
  revert Phin Pgin,
  rewrite [-Pj, *fin_lcoset_same],
  intro Pheq Pgeq,
  rewrite [*(lrcoset_same_of_mem_normalizer Pkin), *fin_lrcoset_comm, Pheq, Pgeq]
end

lemma lcoset_mul_is_lcoset (J K : lcoset_type (normalizer H) H) :
  is_fin_lcoset (normalizer H) H (lcoset_mul J K) :=
obtain j Pjin Pj, from has_property J,
obtain k Pkin Pk, from has_property K,
exists.intro (j*k) (and.intro (finsubg_mul_closed _ Pjin Pkin)
  begin rewrite [lcoset_mul_eq_lcoset J K (Pj ▸ fin_mem_lcoset j), -fin_lcoset_compose, Pk] end)

lemma lcoset_inv_is_lcoset (J : lcoset_type (normalizer H) H) :
  is_fin_lcoset (normalizer H) H (fin_inv (elt_of J)) :=
obtain j Pjin Pj, from has_property J, exists.intro j⁻¹
begin
  rewrite [-Pj, finsubg_inv_lcoset_eq_rcoset],
  apply and.intro,
    apply normalizer_has_inv, assumption,
    apply lrcoset_same_of_mem_normalizer, apply normalizer_has_inv, assumption
end

definition fin_coset_mul (J K : lcoset_type (normalizer H) H) : lcoset_type (normalizer H) H :=
tag (lcoset_mul J K) (lcoset_mul_is_lcoset J K)

definition fin_coset_inv (J : lcoset_type (normalizer H) H) : lcoset_type (normalizer H) H :=
tag (fin_inv (elt_of J)) (lcoset_inv_is_lcoset J)

definition fin_coset_one : lcoset_type (normalizer H) H :=
tag H self_is_lcoset

local infix `^` := fin_coset_mul

lemma fin_coset_mul_eq_lcoset (J K : lcoset_type (normalizer H) H) {g : G} :
  g ∈ (elt_of J) → elt_of (J ^ K) = fin_lcoset (elt_of K) g :=
assume Pgin, lcoset_mul_eq_lcoset J K Pgin

lemma fin_coset_mul_assoc (J K L : lcoset_type (normalizer H) H) :
  J ^ K ^ L = J ^ (K ^ L) :=
obtain j Pjin Pj, from exists_of_lcoset_type J,
obtain k Pkin Pk, from exists_of_lcoset_type K,
assert Pjk : j*k ∈ elt_of (J ^ K), from mul_mem_lcoset_mul J K Pjin Pkin,
obtain l Plin Pl, from has_property L,
subtype.eq (begin
  rewrite [fin_coset_mul_eq_lcoset (J ^ K) _ Pjk,
    fin_coset_mul_eq_lcoset J _ Pjin,
    fin_coset_mul_eq_lcoset K _ Pkin,
    -Pl, *fin_lcoset_compose]
  end)

lemma fin_coset_mul_one (J : lcoset_type (normalizer H) H) :
  J ^ fin_coset_one = J :=
obtain j Pjin Pj, from exists_of_lcoset_type J,
subtype.eq begin
  rewrite [↑fin_coset_one, fin_coset_mul_eq_lcoset _ _ Pjin, -Pj]
end

lemma fin_coset_one_mul (J : lcoset_type (normalizer H) H) :
  fin_coset_one ^ J = J :=
subtype.eq begin
  rewrite [↑fin_coset_one, fin_coset_mul_eq_lcoset _ _ (finsubg_has_one H), fin_lcoset_id]
end

lemma fin_coset_left_inv (J : lcoset_type (normalizer H) H) :
  (fin_coset_inv J) ^ J = fin_coset_one :=
obtain j Pjin Pj, from exists_of_lcoset_type J,
assert Pjinv : j⁻¹ ∈ elt_of (fin_coset_inv J), from inv_mem_fin_inv Pjin,
subtype.eq begin
  rewrite [↑fin_coset_one, fin_coset_mul_eq_lcoset _ _ Pjinv, -Pj, fin_lcoset_inv]
end

variable (H)

definition fin_coset_group [instance] : group (lcoset_type (normalizer H) H) :=
group.mk fin_coset_mul fin_coset_mul_assoc fin_coset_one fin_coset_one_mul fin_coset_mul_one fin_coset_inv fin_coset_left_inv

variables {H} (Hc : finset (lcoset_type (normalizer H) H))

definition fin_coset_Union : finset G := Union Hc elt_of

variables {Hc} [finsubgHc : is_finsubg Hc]
include finsubgHc

lemma mem_normalizer_of_mem_fcU {j : G} : j ∈ fin_coset_Union Hc → j ∈ normalizer H :=
assume Pjin, obtain J PJ PjJ, from iff.elim_left !mem_Union_iff Pjin,
mem_of_subset_of_mem !lcoset_subset_normalizer PjJ

lemma fcU_has_one : (1:G) ∈ fin_coset_Union Hc :=
iff.elim_right (mem_Union_iff Hc elt_of (1:G))
  (exists.intro 1 (and.intro (finsubg_has_one Hc) (finsubg_has_one H)))

lemma fcU_has_inv : finset_has_inv (fin_coset_Union Hc) :=
take j, assume Pjin, obtain J PJ PjJ, from iff.elim_left !mem_Union_iff Pjin,
have PJinv : J⁻¹ ∈ Hc, from finsubg_has_inv Hc PJ,
have Pjinv : j⁻¹ ∈ elt_of J⁻¹, from inv_mem_fin_inv PjJ,
iff.elim_right !mem_Union_iff (exists.intro J⁻¹ (and.intro PJinv Pjinv))

lemma fcU_mul_closed : finset_mul_closed_on (fin_coset_Union Hc) :=
take j k, assume Pjin Pkin,
obtain J PJ PjJ, from iff.elim_left !mem_Union_iff Pjin,
obtain K PK PkK, from iff.elim_left !mem_Union_iff Pkin,
assert Pjk : j*k ∈ elt_of (J*K), from mul_mem_lcoset_mul J K PjJ PkK,
iff.elim_right !mem_Union_iff
  (exists.intro (J*K) (and.intro (finsubg_mul_closed Hc PJ PK) Pjk))

definition fcU_is_finsubg [instance] : is_finsubg (fin_coset_Union Hc) :=
is_finsubg.mk fcU_has_one fcU_mul_closed fcU_has_inv

end normalizer

end group
