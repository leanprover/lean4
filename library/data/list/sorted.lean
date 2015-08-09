/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import data.list.comb

namespace list
variable {A : Type}
variable (R : A → A → Prop)

inductive locally_sorted : list A → Prop :=
| base0 : locally_sorted []
| base  : ∀ a, locally_sorted [a]
| step  : ∀ {a b l}, R a b → locally_sorted (b::l) → locally_sorted (a::b::l)

inductive hd_rel (a : A) : list A → Prop :=
| base : hd_rel a []
| step : ∀ {b} (l), R a b → hd_rel a (b::l)

inductive sorted : list A → Prop :=
| base : sorted []
| step : ∀ {a : A} {l : list A}, hd_rel R a l → sorted l → sorted (a::l)

variable {R}

lemma hd_rel_inv : ∀ {a b l}, hd_rel R a (b::l) → R a b :=
begin intros a b l h, cases h, assumption end

lemma sorted_inv : ∀ {a l}, sorted R (a::l) → hd_rel R a l ∧ sorted R l :=
begin intros a l h, cases h, split, repeat assumption end

lemma sorted.rect_on {P : list A → Type} : ∀ {l}, sorted R l → P [] → (∀ a l, sorted R l → P l → hd_rel R a l → P (a::l)) → P l
| []     s h₁ h₂ := h₁
| (a::l) s h₁ h₂ :=
  have hd_rel R a l, from and.left (sorted_inv s),
  have sorted R l,   from and.right (sorted_inv s),
  have P l,          from sorted.rect_on this h₁ h₂,
  h₂ a l `sorted R l` `P l` `hd_rel R a l`

lemma sorted_singleton (a : A) : sorted R [a] :=
sorted.step !hd_rel.base !sorted.base


lemma sorted_of_locally_sorted : ∀ {l}, locally_sorted R l → sorted R l
| []        h := !sorted.base
| [a]       h := !sorted_singleton
| (a::b::l) (locally_sorted.step h₁ h₂) :=
  have sorted R (b::l), from sorted_of_locally_sorted h₂,
  sorted.step (hd_rel.step _ h₁) this

lemma locally_sorted_of_sorted : ∀ {l}, sorted R l → locally_sorted R l
| []        h := !locally_sorted.base0
| [a]       h := !locally_sorted.base
| (a::b::l) (sorted.step (hd_rel.step _ h₁) h₂) :=
  have locally_sorted R (b::l), from locally_sorted_of_sorted h₂,
  locally_sorted.step h₁ this

lemma strongly_sorted_eq_sorted : @locally_sorted = @sorted :=
funext (λ A, funext (λ R, funext (λ l, propext (iff.intro sorted_of_locally_sorted locally_sorted_of_sorted))))

variable (R)

inductive strongly_sorted : list A → Prop :=
| base : strongly_sorted []
| step : ∀ {a l}, all l (R a) → strongly_sorted l → strongly_sorted (a::l)

variable {R}

lemma sorted_of_strongly_sorted : ∀ {l}, strongly_sorted R l → sorted R l
| []        h := !sorted.base
| [a]       h := !sorted_singleton
| (a::b::l) (strongly_sorted.step h₁ h₂) :=
  have hd_rel R a (b::l), from hd_rel.step _ (of_all_cons h₁),
  have sorted R (b::l),   from sorted_of_strongly_sorted h₂,
  sorted.step `hd_rel R a (b::l)` `sorted R (b::l)`

lemma sorted_extends (trans : transitive R) : ∀ {a l}, sorted R (a::l) → all l (R a)
| a []     h := !all_nil
| a (b::l) h :=
  have hd_rel R a (b::l), from and.left (sorted_inv h),
  have R a b,             from hd_rel_inv this,
  have all l (R b),       from sorted_extends (and.right (sorted_inv h)),
  all_of_forall (take x, suppose x ∈ b::l,
    or.elim (eq_or_mem_of_mem_cons this)
      (suppose x = b, by+ subst x; assumption)
      (suppose x ∈ l,
        have R b x, from of_mem_of_all this `all l (R b)`,
        trans `R a b` `R b x`))

theorem strongly_sorted_of_sorted_of_transitive (trans : transitive R) : ∀ {l}, sorted R l → strongly_sorted R l
| []     h := !strongly_sorted.base
| (a::l) h :=
  have sorted R l,          from and.right (sorted_inv h),
  have strongly_sorted R l, from strongly_sorted_of_sorted_of_transitive this,
  have all l (R a),         from sorted_extends trans h,
  strongly_sorted.step `all l (R a)` `strongly_sorted R l`
end list
