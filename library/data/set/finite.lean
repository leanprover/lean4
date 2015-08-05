/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

The notion of "finiteness" for sets. This approach is not computational: for example, just because
an element  s : set A  satsifies  finite s  doesn't mean that we can compute the cardinality. For
a computational representation, use the finset type.

-/
import data.set.function data.finset logic.choice
open [coercions] finset nat

variable {A : Type}

namespace set

definition finite [class] (s : set A) : Prop := ∃ (s' : finset A), s = finset.to_set s'

theorem finite_of_finset [instance] (s : finset A) : finite s :=
exists.intro s rfl

noncomputable definition finset_of_finite (s : set A) [fins : finite s] : finset A := some fins

theorem to_set_of_finset_of_finite (s : set A) [fins : finite s] :
  finset.to_set (finset_of_finite s) = s :=
eq.symm (some_spec fins)

-- this casts every set to a finite set
noncomputable definition to_finset (s : set A) : finset A :=
if fins : finite s then finset_of_finite s else finset.empty

theorem to_set_of_to_finset_of_finite (s : set A) [fins : finite s] :
  finset.to_set (to_finset s) = s :=
by rewrite [↑set.to_finset, dif_pos fins]; apply to_set_of_finset_of_finite

theorem to_set_of_to_finset_of_not_finite {s : set A} (nfins : ¬ finite s) : to_finset s = ∅ :=
by rewrite [↑set.to_finset, dif_neg nfins]

theorem to_finset_of_to_set (s : finset A) : to_finset (finset.to_set s) = s :=
by rewrite [finset.eq_eq_to_set_eq, to_set_of_to_finset_of_finite s]

/- finiteness -/

theorem finite_empty [instance] : finite (∅ : set A) :=
exists.intro finset.empty (by rewrite [finset.to_set_empty])

theorem finite_insert [instance] (a : A) (s : set A) [fins : finite s] : finite (insert a s) :=
exists.intro (finset.insert a (finset_of_finite s))
  (by rewrite [finset.to_set_insert, to_set_of_finset_of_finite])

example : finite '{1, 2, 3} := _

theorem finite_union [instance] (s t : set A) [fins : finite s] [fint : finite t] :
  finite (s ∪ t) :=
exists.intro (#finset finset_of_finite s ∪ finset_of_finite t)
  (by rewrite [finset.to_set_union, *to_set_of_finset_of_finite])

theorem finite_inter [instance] (s t : set A) [fins : finite s] [fint : finite t] :
  finite (s ∩ t) :=
exists.intro (#finset finset_of_finite s ∩ finset_of_finite t)
  (by rewrite [finset.to_set_inter, *to_set_of_finset_of_finite])

theorem finite_filter [instance] (s : set A) (p : A → Prop) [h : decidable_pred p]
    [fins : finite s] :
  finite {x ∈ s | p x}  :=
exists.intro (finset.filter p (finset_of_finite s))
  (by rewrite [finset.to_set_filter, *to_set_of_finset_of_finite])

theorem finite_image [instance] {B : Type} [h : decidable_eq B] (f : A → B) (s : finset A)
    [fins : finite s] :
  finite (f '[s]) :=
exists.intro (finset.image f (finset_of_finite s))
  (by rewrite [finset.to_set_image, *to_set_of_finset_of_finite])

theorem finite_diff [instance] (s t : set A) [fins : finite s] : finite (s \ t) :=
!finite_filter

theorem finite_subset {s t : set A} [fint : finite t] (ssubt : s ⊆ t) : finite s :=
by rewrite (eq_filter_of_subset ssubt); apply finite_filter

/- cardinality -/

noncomputable definition card (s : set A) := finset.card (set.to_finset s)

theorem card_of_finset (s : finset A) : card s = finset.card s :=
by rewrite [↑card, to_finset_of_to_set]

theorem card_add_card (s₁ s₂ : set A) [fins₁ : finite s₁] [fins₂ : finite s₂] :
  card s₁ + card s₂ = card (s₁ ∪ s₂) + card (s₁ ∩ s₂) :=
begin
  rewrite [-to_set_of_to_finset_of_finite s₁, -to_set_of_to_finset_of_finite s₂],
  rewrite [-finset.to_set_union, -finset.to_set_inter, *card_of_finset],
  apply finset.card_add_card
end

end set
