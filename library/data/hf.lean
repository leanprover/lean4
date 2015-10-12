/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Hereditarily finite sets: finite sets whose elements are all hereditarily finite sets.

Remark: all definitions compute, however the performace is quite poor since
we implement this module using a bijection from (finset nat) to nat, and
this bijection is implemeted using the Ackermann coding.
-/
import data.nat data.finset.equiv data.list
open nat binary algebra
open - [notations] finset

definition hf := nat

namespace hf
local attribute hf [reducible]

protected definition prio : num := num.succ std.priority.default

protected definition is_inhabited [instance] : inhabited hf :=
nat.is_inhabited

protected definition has_decidable_eq [reducible] [instance] : decidable_eq hf :=
nat.has_decidable_eq

definition of_finset (s : finset hf) : hf :=
@equiv.to_fun _ _ finset_nat_equiv_nat s

definition to_finset (h : hf) : finset hf :=
@equiv.inv _ _ finset_nat_equiv_nat h

definition to_nat (h : hf) : nat :=
h

definition of_nat (n : nat) : hf :=
n

lemma to_finset_of_finset (s : finset hf) : to_finset (of_finset s) = s :=
@equiv.left_inv _ _ finset_nat_equiv_nat s

lemma of_finset_to_finset (s : hf) : of_finset (to_finset s) = s :=
@equiv.right_inv _ _ finset_nat_equiv_nat s

lemma to_finset_inj {s₁ s₂ : hf} : to_finset s₁ = to_finset s₂ → s₁ = s₂ :=
λ h, function.injective_of_left_inverse of_finset_to_finset h

lemma of_finset_inj {s₁ s₂ : finset hf} : of_finset s₁ = of_finset s₂ → s₁ = s₂ :=
λ h, function.injective_of_left_inverse to_finset_of_finset h

/- empty -/
definition empty : hf :=
of_finset (finset.empty)

notation `∅` := hf.empty

/- insert -/
definition insert (a s : hf) : hf :=
of_finset (finset.insert a (to_finset s))

/- mem -/
definition mem (a : hf) (s : hf) : Prop :=
finset.mem a (to_finset s)

infix ∈ := mem
notation [priority finset.prio] a ∉ b := ¬ mem a b

lemma insert_lt_of_not_mem {a s : hf} : a ∉ s → s < insert a s :=
begin
  unfold [insert, of_finset, equiv.to_fun, finset_nat_equiv_nat, mem, to_finset, equiv.inv],
  intro h,
  rewrite [finset.to_nat_insert h],
  rewrite [to_nat_of_nat, -zero_add s at {1}],
  apply add_lt_add_right,
  apply pow_pos_of_pos _ dec_trivial
end

lemma insert_lt_insert_of_not_mem_of_not_mem_of_lt {a s₁ s₂ : hf}
      : a ∉ s₁ → a ∉ s₂ → s₁ < s₂ → insert a s₁ < insert a s₂ :=
begin
  unfold [insert, of_finset, equiv.to_fun, finset_nat_equiv_nat, mem, to_finset, equiv.inv],
  intro h₁ h₂ h₃,
  rewrite [finset.to_nat_insert h₁],
  rewrite [finset.to_nat_insert h₂, *to_nat_of_nat],
  apply add_lt_add_left h₃
end

open decidable
protected definition decidable_mem [instance] : ∀ a s, decidable (a ∈ s) :=
λ a s, finset.decidable_mem a (to_finset s)

lemma insert_le (a s : hf) : s ≤ insert a s :=
by_cases
  (suppose a ∈ s, by rewrite [↑insert, insert_eq_of_mem this, of_finset_to_finset])
  (suppose a ∉ s, le_of_lt (insert_lt_of_not_mem this))

lemma not_mem_empty (a : hf) : a ∉ ∅ :=
begin unfold [mem, empty], rewrite to_finset_of_finset, apply finset.not_mem_empty end

lemma mem_insert (a s : hf) : a ∈ insert a s :=
begin unfold [mem, insert], rewrite to_finset_of_finset, apply finset.mem_insert end

lemma mem_insert_of_mem {a s : hf} (b : hf) : a ∈ s → a ∈ insert b s :=
begin unfold [mem, insert], intros, rewrite to_finset_of_finset, apply finset.mem_insert_of_mem, assumption end

lemma eq_or_mem_of_mem_insert {a b s : hf} : a ∈ insert b s → a = b ∨ a ∈ s :=
begin unfold [mem, insert], rewrite to_finset_of_finset, intros, apply eq_or_mem_of_mem_insert, assumption  end

theorem mem_of_mem_insert_of_ne {x a : hf} {s : hf} : x ∈ insert a s → x ≠ a → x ∈ s :=
begin unfold [mem, insert], rewrite to_finset_of_finset, intros, apply mem_of_mem_insert_of_ne, repeat assumption end

protected theorem ext {s₁ s₂ : hf} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ :=
assume h,
assert to_finset s₁ = to_finset s₂, from finset.ext h,
assert of_finset (to_finset s₁) = of_finset (to_finset s₂), by rewrite this,
by rewrite [*of_finset_to_finset at this]; exact this

theorem insert_eq_of_mem {a : hf} {s : hf} : a ∈ s → insert a s = s :=
begin unfold mem, intro h, unfold [mem, insert], rewrite (finset.insert_eq_of_mem h), rewrite of_finset_to_finset end

protected theorem induction [recursor 4] {P : hf → Prop}
    (h₁ : P empty) (h₂ : ∀ (a s : hf), a ∉ s → P s → P (insert a s)) (s : hf) : P s :=
assert P (of_finset (to_finset s)), from
  @finset.induction _ _ _ h₁
    (λ a s nain ih,
       begin
         unfold [mem, insert] at h₂,
         rewrite -(to_finset_of_finset s) at nain,
         have P (insert a (of_finset s)), by exact h₂ a (of_finset s) nain ih,
         rewrite [↑insert at this, to_finset_of_finset at this],
         exact this
       end)
    (to_finset s),
by rewrite of_finset_to_finset at this; exact this

lemma insert_le_insert_of_le {a s₁ s₂ : hf} : a ∈ s₁ ∨ a ∉ s₂ → s₁ ≤ s₂ → insert a s₁ ≤ insert a s₂ :=
suppose a ∈ s₁ ∨ a ∉ s₂,
suppose s₁ ≤ s₂,
by_cases
  (suppose s₁ = s₂, by rewrite this)
  (suppose s₁ ≠ s₂,
    have s₁ < s₂, from lt_of_le_of_ne `s₁ ≤ s₂` `s₁ ≠ s₂`,
    by_cases
      (suppose a ∈ s₁, by_cases
        (suppose a ∈ s₂, by rewrite [insert_eq_of_mem `a ∈ s₁`, insert_eq_of_mem `a ∈ s₂`]; assumption)
        (suppose a ∉ s₂, by rewrite [insert_eq_of_mem `a ∈ s₁`]; exact le.trans `s₁ ≤ s₂` !insert_le))
      (suppose a ∉ s₁, by_cases
        (suppose a ∈ s₂, or.elim `a ∈ s₁ ∨ a ∉ s₂` (by contradiction) (by contradiction))
        (suppose a ∉ s₂, le_of_lt (insert_lt_insert_of_not_mem_of_not_mem_of_lt `a ∉ s₁` `a ∉ s₂` `s₁ < s₂`))))

/- union -/
definition union (s₁ s₂ : hf) : hf :=
of_finset (finset.union (to_finset s₁) (to_finset s₂))

infix [priority hf.prio] ∪ := union

theorem mem_union_left {a : hf} {s₁ : hf} (s₂ : hf) : a ∈ s₁ → a ∈ s₁ ∪ s₂ :=
begin unfold mem, intro h, unfold union, rewrite to_finset_of_finset, apply finset.mem_union_left _ h end

theorem mem_union_l {a : hf} {s₁ : hf} {s₂ : hf} : a ∈ s₁ → a ∈ s₁ ∪ s₂ :=
mem_union_left s₂

theorem mem_union_right {a : hf} {s₂ : hf} (s₁ : hf) : a ∈ s₂ → a ∈ s₁ ∪ s₂ :=
begin unfold mem, intro h, unfold union, rewrite to_finset_of_finset, apply finset.mem_union_right _ h end

theorem mem_union_r {a : hf} {s₂ : hf} {s₁ : hf} : a ∈ s₂ → a ∈ s₁ ∪ s₂ :=
mem_union_right s₁

theorem mem_or_mem_of_mem_union {a : hf} {s₁ s₂ : hf} : a ∈ s₁ ∪ s₂ → a ∈ s₁ ∨ a ∈ s₂ :=
begin unfold [mem, union], rewrite to_finset_of_finset, intro h, apply finset.mem_or_mem_of_mem_union h end

theorem mem_union_iff {a : hf} (s₁ s₂ : hf) : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ :=
iff.intro
 (λ h, mem_or_mem_of_mem_union h)
 (λ d, or.elim d
   (λ i, mem_union_left _ i)
   (λ i, mem_union_right _ i))

theorem mem_union_eq {a : hf} (s₁ s₂ : hf) : (a ∈ s₁ ∪ s₂) = (a ∈ s₁ ∨ a ∈ s₂) :=
propext !mem_union_iff

theorem union.comm (s₁ s₂ : hf) : s₁ ∪ s₂ = s₂ ∪ s₁ :=
hf.ext (λ a, by rewrite [*mem_union_eq]; exact or.comm)

theorem union.assoc (s₁ s₂ s₃ : hf) : (s₁ ∪ s₂) ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) :=
hf.ext (λ a, by rewrite [*mem_union_eq]; exact or.assoc)

theorem union.left_comm (s₁ s₂ s₃ : hf) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
!left_comm union.comm union.assoc s₁ s₂ s₃

theorem union.right_comm (s₁ s₂ s₃ : hf) : (s₁ ∪ s₂) ∪ s₃ = (s₁ ∪ s₃) ∪ s₂ :=
!right_comm union.comm union.assoc s₁ s₂ s₃

theorem union_self (s : hf) : s ∪ s = s :=
hf.ext (λ a, iff.intro
  (λ ain, or.elim (mem_or_mem_of_mem_union ain) (λ i, i) (λ i, i))
  (λ i, mem_union_left _ i))

theorem union_empty (s : hf) : s ∪ ∅ = s :=
hf.ext (λ a, iff.intro
  (suppose a ∈ s ∪ ∅, or.elim (mem_or_mem_of_mem_union this) (λ i, i) (λ i, absurd i !not_mem_empty))
  (suppose a ∈ s, mem_union_left _ this))

theorem empty_union (s : hf) : ∅ ∪ s = s :=
calc ∅ ∪ s = s ∪ ∅ : union.comm
       ... = s     : union_empty

/- inter -/
definition inter (s₁ s₂ : hf) : hf :=
of_finset (finset.inter (to_finset s₁) (to_finset s₂))

infix [priority hf.prio] ∩ := inter

theorem mem_of_mem_inter_left {a : hf} {s₁ s₂ : hf} : a ∈ s₁ ∩ s₂ → a ∈ s₁ :=
begin unfold mem, unfold inter, rewrite to_finset_of_finset, intro h, apply finset.mem_of_mem_inter_left h end

theorem mem_of_mem_inter_right {a : hf} {s₁ s₂ : hf} : a ∈ s₁ ∩ s₂ → a ∈ s₂ :=
begin unfold mem, unfold inter, rewrite to_finset_of_finset, intro h, apply finset.mem_of_mem_inter_right h end

theorem mem_inter {a : hf} {s₁ s₂ : hf} : a ∈ s₁ → a ∈ s₂ → a ∈ s₁ ∩ s₂ :=
begin unfold mem, intro h₁ h₂, unfold inter, rewrite to_finset_of_finset, apply finset.mem_inter h₁ h₂ end

theorem mem_inter_iff (a : hf) (s₁ s₂ : hf) : a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂ :=
iff.intro
 (λ h, and.intro (mem_of_mem_inter_left h) (mem_of_mem_inter_right h))
 (λ h, mem_inter (and.elim_left h) (and.elim_right h))

theorem mem_inter_eq (a : hf) (s₁ s₂ : hf) : (a ∈ s₁ ∩ s₂) = (a ∈ s₁ ∧ a ∈ s₂) :=
propext !mem_inter_iff

theorem inter.comm (s₁ s₂ : hf) : s₁ ∩ s₂ = s₂ ∩ s₁ :=
hf.ext (λ a, by rewrite [*mem_inter_eq]; exact and.comm)

theorem inter.assoc (s₁ s₂ s₃ : hf) : (s₁ ∩ s₂) ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) :=
hf.ext (λ a, by rewrite [*mem_inter_eq]; exact and.assoc)

theorem inter.left_comm (s₁ s₂ s₃ : hf) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
!left_comm inter.comm inter.assoc s₁ s₂ s₃

theorem inter.right_comm (s₁ s₂ s₃ : hf) : (s₁ ∩ s₂) ∩ s₃ = (s₁ ∩ s₃) ∩ s₂ :=
!right_comm inter.comm inter.assoc s₁ s₂ s₃

theorem inter_self (s : hf) : s ∩ s = s :=
hf.ext (λ a, iff.intro
  (λ h, mem_of_mem_inter_right h)
  (λ h, mem_inter h h))

theorem inter_empty (s : hf) : s ∩ ∅ = ∅ :=
hf.ext (λ a, iff.intro
  (suppose a ∈ s ∩ ∅, absurd (mem_of_mem_inter_right this) !not_mem_empty)
  (suppose a ∈ ∅,     absurd this !not_mem_empty))

theorem empty_inter (s : hf) : ∅ ∩ s = ∅ :=
calc ∅ ∩ s = s ∩ ∅ : inter.comm
       ... = ∅     : inter_empty

/- card -/
definition card (s : hf) : nat :=
finset.card (to_finset s)

theorem card_empty : card ∅ = 0 :=
rfl

lemma ne_empty_of_card_eq_succ {s : hf} {n : nat} : card s = succ n → s ≠ ∅ :=
by intros; substvars; contradiction

/- erase -/
definition erase (a : hf) (s : hf) : hf :=
of_finset (erase a (to_finset s))

theorem mem_erase (a : hf) (s : hf) : a ∉ erase a s :=
begin unfold [mem, erase], rewrite to_finset_of_finset, apply finset.mem_erase end

theorem card_erase_of_mem {a : hf} {s : hf} : a ∈ s → card (erase a s) = pred (card s) :=
begin unfold mem, intro h, unfold [erase, card], rewrite to_finset_of_finset, apply finset.card_erase_of_mem h end

theorem card_erase_of_not_mem {a : hf} {s : hf} : a ∉ s → card (erase a s) = card s :=
begin unfold [mem], intro h, unfold [erase, card], rewrite to_finset_of_finset, apply finset.card_erase_of_not_mem h end

theorem erase_empty (a : hf) : erase a ∅ = ∅ :=
rfl

theorem ne_of_mem_erase {a b : hf} {s : hf} : b ∈ erase a s → b ≠ a :=
by intro h beqa; subst b; exact absurd h !mem_erase

theorem mem_of_mem_erase {a b : hf} {s : hf} : b ∈ erase a s → b ∈ s :=
begin unfold [erase, mem], rewrite to_finset_of_finset, intro h, apply mem_of_mem_erase h end

theorem mem_erase_of_ne_of_mem {a b : hf} {s : hf} : a ≠ b → a ∈ s → a ∈ erase b s :=
begin intro h₁, unfold mem, intro h₂, unfold erase, rewrite to_finset_of_finset, apply mem_erase_of_ne_of_mem h₁ h₂ end

theorem mem_erase_iff (a b : hf) (s : hf) : a ∈ erase b s ↔ a ∈ s ∧ a ≠ b :=
iff.intro
  (assume H, and.intro (mem_of_mem_erase H) (ne_of_mem_erase H))
  (assume H, mem_erase_of_ne_of_mem (and.right H) (and.left H))

theorem mem_erase_eq (a b : hf) (s : hf) : a ∈ erase b s = (a ∈ s ∧ a ≠ b) :=
propext !mem_erase_iff

theorem erase_insert {a : hf} {s : hf} : a ∉ s → erase a (insert a s) = s :=
begin
  unfold [mem, erase, insert],
  intro h, rewrite [to_finset_of_finset, finset.erase_insert h, of_finset_to_finset]
end

theorem insert_erase {a : hf} {s : hf} : a ∈ s → insert a (erase a s) = s :=
begin
  unfold mem, intro h, unfold [insert, erase],
  rewrite [to_finset_of_finset, finset.insert_erase h, of_finset_to_finset]
end


/- subset -/
definition subset (s₁ s₂ : hf) : Prop :=
finset.subset (to_finset s₁) (to_finset s₂)

infix [priority hf.prio] ⊆ := subset

theorem empty_subset (s : hf) : ∅ ⊆ s :=
begin unfold [empty, subset], rewrite to_finset_of_finset, apply finset.empty_subset (to_finset s) end

theorem subset.refl (s : hf) : s ⊆ s :=
begin unfold [subset], apply finset.subset.refl (to_finset s) end

theorem subset.trans {s₁ s₂ s₃ : hf} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ :=
begin unfold [subset], intro h₁ h₂, apply finset.subset.trans h₁ h₂ end

theorem mem_of_subset_of_mem {s₁ s₂ : hf} {a : hf} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ :=
begin unfold [subset, mem], intro h₁ h₂, apply finset.mem_of_subset_of_mem h₁ h₂ end

theorem subset.antisymm {s₁ s₂ : hf} : s₁ ⊆ s₂ → s₂ ⊆ s₁ → s₁ = s₂ :=
begin unfold [subset], intro h₁ h₂, apply to_finset_inj (finset.subset.antisymm h₁ h₂) end

-- alternative name
theorem eq_of_subset_of_subset {s₁ s₂ : hf} (H₁ : s₁ ⊆ s₂) (H₂ : s₂ ⊆ s₁) : s₁ = s₂ :=
subset.antisymm H₁ H₂

theorem subset_of_forall {s₁ s₂ : hf} : (∀x, x ∈ s₁ → x ∈ s₂) → s₁ ⊆ s₂ :=
begin unfold [mem, subset], intro h, apply finset.subset_of_forall h end

theorem subset_insert (s : hf) (a : hf) : s ⊆ insert a s :=
begin unfold [subset, insert], rewrite to_finset_of_finset, apply finset.subset_insert (to_finset s) end

theorem eq_empty_of_subset_empty {x : hf} (H : x ⊆ ∅) : x = ∅ :=
subset.antisymm H (empty_subset x)

theorem subset_empty_iff (x : hf) : x ⊆ ∅ ↔ x = ∅ :=
iff.intro eq_empty_of_subset_empty (take xeq, by rewrite xeq; apply subset.refl ∅)

theorem erase_subset_erase (a : hf) {s t : hf} : s ⊆ t → erase a s ⊆ erase a t :=
begin unfold [subset, erase], intro h, rewrite *to_finset_of_finset, apply finset.erase_subset_erase a h end

theorem erase_subset  (a : hf) (s : hf) : erase a s ⊆ s :=
begin unfold [subset, erase], rewrite to_finset_of_finset, apply finset.erase_subset a (to_finset s) end

theorem erase_eq_of_not_mem {a : hf} {s : hf} : a ∉ s → erase a s = s :=
begin unfold [mem, erase], intro h, rewrite [finset.erase_eq_of_not_mem h, of_finset_to_finset] end

theorem erase_insert_subset (a : hf) (s : hf) : erase a (insert a s) ⊆ s :=
begin unfold [erase, insert, subset], rewrite [*to_finset_of_finset], apply finset.erase_insert_subset a (to_finset s) end

theorem erase_subset_of_subset_insert {a : hf} {s t : hf} (H : s ⊆ insert a t) : erase a s ⊆ t :=
hf.subset.trans (!hf.erase_subset_erase H) (erase_insert_subset a t)

theorem insert_erase_subset (a : hf) (s : hf) : s ⊆ insert a (erase a s) :=
decidable.by_cases
  (assume ains : a ∈ s, by rewrite [!insert_erase ains]; apply subset.refl)
  (assume nains : a ∉ s,
    suffices s ⊆ insert a s, by rewrite [erase_eq_of_not_mem nains]; assumption,
    subset_insert s a)

theorem insert_subset_insert (a : hf) {s t : hf} : s ⊆ t → insert a s ⊆ insert a t :=
begin
  unfold [subset, insert], intro h,
  rewrite *to_finset_of_finset, apply finset.insert_subset_insert a h
end

theorem subset_insert_of_erase_subset {s t : hf} {a : hf} (H : erase a s ⊆ t) : s ⊆ insert a t :=
subset.trans (insert_erase_subset a s) (!insert_subset_insert H)

theorem subset_insert_iff (s t : hf) (a : hf) : s ⊆ insert a t ↔ erase a s ⊆ t :=
iff.intro !erase_subset_of_subset_insert !subset_insert_of_erase_subset

theorem le_of_subset {s₁ s₂ : hf} : s₁ ⊆ s₂ → s₁ ≤ s₂ :=
begin
  revert s₂, induction s₁ with a s₁ nain ih,
   take s₂, suppose ∅ ⊆ s₂, !zero_le,
   take s₂, suppose insert a s₁ ⊆ s₂,
     assert a ∈ s₂,          from mem_of_subset_of_mem this !mem_insert,
     have   a ∉ erase a s₂,  from !mem_erase,
     have   s₁ ⊆ erase a s₂, from subset_of_forall
       (take x xin, by_cases
         (suppose x = a, by subst x; contradiction)
         (suppose x ≠ a,
           have x ∈ s₂, from mem_of_subset_of_mem `insert a s₁ ⊆ s₂` (mem_insert_of_mem _ `x ∈ s₁`),
           mem_erase_of_ne_of_mem `x ≠ a` `x ∈ s₂`)),
     have   s₁ ≤ erase a s₂, from ih _ this,
     assert insert a s₁ ≤ insert a (erase a s₂), from
       insert_le_insert_of_le (or.inr `a ∉ erase a s₂`) this,
     by rewrite [insert_erase `a ∈ s₂` at this]; exact this
end

/- image -/
definition image (f : hf → hf) (s : hf) : hf :=
of_finset (finset.image f (to_finset s))

theorem image_empty (f : hf → hf) : image f ∅ = ∅ :=
rfl

theorem mem_image_of_mem (f : hf → hf) {s : hf} {a : hf} : a ∈ s → f a ∈ image f s :=
begin unfold [mem, image], intro h, rewrite to_finset_of_finset, apply finset.mem_image_of_mem f h end

theorem mem_image {f : hf → hf} {s : hf} {a : hf} {b : hf} (H1 : a ∈ s) (H2 : f a = b) : b ∈ image f s :=
eq.subst H2 (mem_image_of_mem f H1)

theorem exists_of_mem_image {f : hf → hf} {s : hf} {b : hf} : b ∈ image f s → ∃a, a ∈ s ∧ f a = b :=
begin unfold [mem, image], rewrite to_finset_of_finset, intro h, apply finset.exists_of_mem_image h end

theorem mem_image_iff (f : hf → hf) {s : hf} {y : hf} : y ∈ image f s ↔ ∃x, x ∈ s ∧ f x = y :=
begin unfold [mem, image], rewrite to_finset_of_finset, apply finset.mem_image_iff end

theorem mem_image_eq (f : hf → hf) {s : hf} {y : hf} : y ∈ image f s = ∃x, x ∈ s ∧ f x = y :=
propext (mem_image_iff f)

theorem mem_image_of_mem_image_of_subset {f : hf → hf} {s t : hf} {y : hf} (H1 : y ∈ image f s) (H2 : s ⊆ t) : y ∈ image f t :=
obtain x `x ∈ s` `f x = y`, from exists_of_mem_image H1,
have x ∈ t, from mem_of_subset_of_mem H2 `x ∈ s`,
show y ∈ image f t, from mem_image `x ∈ t` `f x = y`

theorem image_insert (f : hf → hf) (s : hf) (a : hf) : image f (insert a s) = insert (f a) (image f s) :=
begin unfold [image, insert], rewrite [*to_finset_of_finset, finset.image_insert] end

open function
lemma image_compose {f : hf → hf} {g : hf → hf} {s : hf} : image (f∘g) s = image f (image g s) :=
begin unfold image, rewrite [*to_finset_of_finset, finset.image_compose] end

lemma image_subset {a b : hf} (f : hf → hf) : a ⊆ b → image f a ⊆ image f b :=
begin unfold [subset, image], intro h, rewrite *to_finset_of_finset, apply finset.image_subset f h end

theorem image_union (f : hf → hf) (s t : hf) : image f (s ∪ t) = image f s ∪ image f t :=
begin unfold [image, union], rewrite [*to_finset_of_finset, finset.image_union] end

/- powerset -/
definition powerset (s : hf) : hf :=
of_finset (finset.image of_finset (finset.powerset (to_finset s)))

prefix [priority hf.prio] `𝒫`:100 := powerset

theorem powerset_empty : 𝒫 ∅ = insert ∅ ∅ :=
rfl

theorem powerset_insert {a : hf} {s : hf} : a ∉ s → 𝒫 (insert a s) = 𝒫 s ∪ image (insert a) (𝒫 s) :=
begin unfold [mem, powerset, insert, union, image], rewrite [*to_finset_of_finset], intro h,
      have (λ (x : finset hf), of_finset (finset.insert a x)) = (λ (x : finset hf), of_finset (finset.insert a (to_finset (of_finset x)))), from
        funext (λ x, by rewrite to_finset_of_finset),
      rewrite [finset.powerset_insert h, finset.image_union, -*finset.image_compose,↑compose,this]
end

theorem mem_powerset_iff_subset (s : hf) : ∀ x : hf, x ∈ 𝒫 s ↔ x ⊆ s :=
begin
  intro x, unfold [mem, powerset, subset], rewrite [to_finset_of_finset, finset.mem_image_eq], apply iff.intro,
  suppose (∃ (w : finset hf), finset.mem w (finset.powerset (to_finset s)) ∧ of_finset w = x),
    obtain w h₁ h₂, from this,
    begin subst x, rewrite to_finset_of_finset, exact iff.mp !finset.mem_powerset_iff_subset h₁ end,
  suppose finset.subset (to_finset x) (to_finset s),
    assert finset.mem (to_finset x) (finset.powerset (to_finset s)), from iff.mpr !finset.mem_powerset_iff_subset this,
    exists.intro (to_finset x) (and.intro this (of_finset_to_finset x))
end

theorem subset_of_mem_powerset {s t : hf} (H : s ∈ 𝒫 t) : s ⊆ t :=
iff.mp (mem_powerset_iff_subset t s) H

theorem mem_powerset_of_subset {s t : hf} (H : s ⊆ t) : s ∈ 𝒫 t :=
iff.mpr (mem_powerset_iff_subset t s) H

theorem empty_mem_powerset (s : hf) : ∅ ∈ 𝒫 s :=
mem_powerset_of_subset (empty_subset s)

/- hf as lists -/
open - [notations] list

definition of_list (s : list hf) : hf :=
@equiv.to_fun _ _ list_nat_equiv_nat s

definition to_list (h : hf) : list hf :=
@equiv.inv _ _ list_nat_equiv_nat h

lemma to_list_of_list (s : list hf) : to_list (of_list s) = s :=
@equiv.left_inv _ _ list_nat_equiv_nat s

lemma of_list_to_list (s : hf) : of_list (to_list s) = s :=
@equiv.right_inv _ _ list_nat_equiv_nat s

lemma to_list_inj {s₁ s₂ : hf} : to_list s₁ = to_list s₂ → s₁ = s₂ :=
λ h, function.injective_of_left_inverse of_list_to_list h

lemma of_list_inj {s₁ s₂ : list hf} : of_list s₁ = of_list s₂ → s₁ = s₂ :=
λ h, function.injective_of_left_inverse to_list_of_list h

definition nil : hf :=
of_list list.nil

lemma empty_eq_nil : ∅ = nil :=
rfl

definition cons (a l : hf) : hf :=
of_list (list.cons a (to_list l))

infixr :: := cons

lemma cons_ne_nil (a l : hf) : a::l ≠ nil :=
by contradiction

lemma head_eq_of_cons_eq {h₁ h₂ t₁ t₂ : hf} : (h₁::t₁) = (h₂::t₂) → h₁ = h₂ :=
begin unfold cons, intro h, apply list.head_eq_of_cons_eq (of_list_inj h) end

lemma tail_eq_of_cons_eq {h₁ h₂ t₁ t₂ : hf} : (h₁::t₁) = (h₂::t₂) → t₁ = t₂ :=
begin unfold cons, intro h, apply to_list_inj (list.tail_eq_of_cons_eq (of_list_inj h)) end

lemma cons_inj {a : hf} : injective (cons a) :=
take l₁ l₂, assume Pe, tail_eq_of_cons_eq Pe

/- append -/
definition append (l₁ l₂ : hf) : hf :=
of_list (list.append (to_list l₁) (to_list l₂))

notation l₁ ++ l₂ := append l₁ l₂

theorem append_nil_left [simp] (t : hf) : nil ++ t = t :=
begin unfold [nil, append], rewrite [to_list_of_list, list.append_nil_left, of_list_to_list] end

theorem append_cons [simp] (x s t : hf) : (x::s) ++ t = x::(s ++ t) :=
begin unfold [cons, append], rewrite [*to_list_of_list, list.append_cons] end

theorem append_nil_right [simp] (t : hf) : t ++ nil = t :=
begin unfold [nil, append], rewrite [to_list_of_list, list.append_nil_right, of_list_to_list] end

theorem append.assoc [simp] (s t u : hf) : s ++ t ++ u = s ++ (t ++ u) :=
begin unfold append, rewrite [*to_list_of_list, list.append.assoc] end

/- length -/
definition length (l : hf) : nat :=
list.length (to_list l)

theorem length_nil [simp] : length nil = 0 :=
begin unfold [length, nil] end

theorem length_cons [simp] (x t : hf) : length (x::t) = length t + 1 :=
begin unfold [length, cons], rewrite to_list_of_list end

theorem length_append [simp] (s t : hf) : length (s ++ t) = length s + length t :=
begin unfold [length, append], rewrite [to_list_of_list, list.length_append] end

theorem eq_nil_of_length_eq_zero {l : hf} : length l = 0 → l = nil :=
begin unfold [length, nil], intro h, rewrite [-list.eq_nil_of_length_eq_zero h, of_list_to_list] end

theorem ne_nil_of_length_eq_succ {l : hf} {n : nat} : length l = succ n → l ≠ nil :=
begin unfold [length, nil], intro h₁ h₂, subst l, rewrite to_list_of_list at h₁, contradiction end

/- head and tail -/
definition head (l : hf) : hf :=
list.head (to_list l)

theorem head_cons [simp] (a l : hf) : head (a::l) = a :=
begin unfold [head, cons], rewrite to_list_of_list end

private lemma to_list_ne_list_nil {s : hf} : s ≠ nil → to_list s ≠ list.nil :=
begin
  unfold nil,
  intro h,
  suppose to_list s = list.nil,
  by rewrite [-this at h, of_list_to_list at h]; exact absurd rfl h
end

theorem head_append [simp] (t : hf) {s : hf} : s ≠ nil → head (s ++ t) = head s :=
begin
  unfold [nil, head, append], rewrite to_list_of_list,
  suppose s ≠ of_list list.nil,
  by rewrite [list.head_append _ (to_list_ne_list_nil this)]
end

definition tail (l : hf) : hf :=
of_list (list.tail (to_list l))

theorem tail_nil [simp] : tail nil = nil :=
begin unfold [tail, nil] end

theorem tail_cons [simp] (a l : hf) : tail (a::l) = l :=
begin unfold [tail, cons], rewrite [to_list_of_list, list.tail_cons, of_list_to_list] end

theorem cons_head_tail {l : hf} : l ≠ nil → (head l)::(tail l) = l :=
begin
  unfold [nil, head, tail, cons],
  suppose l ≠ of_list list.nil,
  by rewrite [to_list_of_list, list.cons_head_tail (to_list_ne_list_nil this), of_list_to_list]
end
end hf
