/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import data.list.comb data.list.perm

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

open perm

lemma eq_of_sorted_of_perm (tr : transitive R) (anti : anti_symmetric R) : ∀ {l₁ l₂ : list A}, l₁ ~ l₂ → sorted R l₁ → sorted R l₂ → l₁ = l₂
| []       []       h₁ h₂ h₃ := rfl
| (a₁::l₁) []       h₁ h₂ h₃ := absurd (perm.symm h₁) !not_perm_nil_cons
| []       (a₂::l₂) h₁ h₂ h₃ := absurd h₁ !not_perm_nil_cons
| (a::l₁)  l₂       h₁ h₂ h₃ :=
  have aux : ∀ {t}, l₂ = a::t → a::l₁ = l₂, from
    take t, suppose l₂ = a::t,
    have   l₁ ~ t,      by rewrite [this at h₁]; apply perm_cons_inv h₁,
    have   sorted R l₁, from and.right (sorted_inv h₂),
    have   sorted R t,  by rewrite [`l₂ = a::t` at h₃]; exact and.right (sorted_inv h₃),
    assert l₁ = t,      from eq_of_sorted_of_perm `l₁ ~ t` `sorted R l₁` `sorted R t`,
    show a :: l₁ = l₂,  by rewrite [`l₂ = a::t`, this],
  have   a ∈ l₂,                       from mem_perm h₁ !mem_cons,
  obtain s t (e₁ : l₂ = s ++ (a::t)),  from mem_split this,
  begin
    cases s with b s,
    { have l₂ = a::t, by exact e₁,
      exact aux this },
    { have e₁   : l₂ = b::(s++(a::t)), by exact e₁,
      have b ∈ l₂,                by rewrite e₁; apply mem_cons,
      have hall₂ : all (s++(a::t)) (R b), begin rewrite [e₁ at h₃], apply sorted_extends tr h₃ end,
      have a ∈ s++(a::t),         from mem_append_right _ !mem_cons,
      have R b a,                 from of_mem_of_all this hall₂,
      have b ∈ a::l₁,             from mem_perm (perm.symm h₁) `b ∈ l₂`,
      have hall₁ : all l₁ (R a),  from sorted_extends tr h₂,
      apply or.elim (eq_or_mem_of_mem_cons `b ∈ a::l₁`),
        suppose b = a,  by rewrite this at e₁; exact aux e₁,
        suppose b ∈ l₁,
          have   R a b, from of_mem_of_all this hall₁,
          assert b = a, from anti `R b a` `R a b`,
          by rewrite this at e₁; exact aux e₁ }
  end
end list
