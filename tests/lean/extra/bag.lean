/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Finite bags.
-/
import data.nat data.list.perm data.subtype algebra.binary
open nat quot list subtype binary function eq.ops
open [declarations] perm

variable {A : Type}

definition bag.setoid [instance] (A : Type) : setoid (list A) :=
setoid.mk (@perm A) (mk_equivalence (@perm A) (@perm.refl A) (@perm.symm A) (@perm.trans A))

definition bag (A : Type) : Type :=
quot (bag.setoid A)

namespace bag
definition of_list (l : list A) : bag A :=
⟦l⟧

definition empty : bag A :=
of_list nil

definition singleton (a : A) : bag A :=
of_list [a]

definition insert (a : A) (b : bag A) : bag A :=
quot.lift_on b (λ l, ⟦a::l⟧)
  (λ l₁ l₂ h, quot.sound (perm.skip a h))

lemma insert_empty_eq_singleton (a : A) : insert a empty = singleton a :=
rfl

definition insert.comm (a₁ a₂ : A) (b : bag A) : insert a₁ (insert a₂ b) = insert a₂ (insert a₁ b) :=
quot.induction_on b (λ l, quot.sound !perm.swap)

definition append (b₁ b₂ : bag A) : bag A :=
quot.lift_on₂ b₁ b₂ (λ l₁ l₂, ⟦l₁++l₂⟧)
  (λ l₁ l₂ l₃ l₄ h₁ h₂, quot.sound (perm_app h₁ h₂))

infix ++ := append

lemma append.comm (b₁ b₂ : bag A) : b₁ ++ b₂ = b₂ ++ b₁ :=
quot.induction_on₂ b₁ b₂ (λ l₁ l₂, quot.sound !perm_app_comm)

lemma append.assoc (b₁ b₂ b₃ : bag A) : (b₁ ++ b₂) ++ b₃ = b₁ ++ (b₂ ++ b₃) :=
quot.induction_on₃ b₁ b₂ b₃ (λ l₁ l₂ l₃, quot.sound (by rewrite list.append.assoc; apply perm.refl))

lemma append_empty_left (b : bag A) : empty ++ b = b :=
quot.induction_on b (λ l, quot.sound (by rewrite append_nil_left; apply perm.refl))

lemma append_empty_right (b : bag A) : b ++ empty = b :=
quot.induction_on b (λ l, quot.sound (by rewrite append_nil_right; apply perm.refl))

lemma append_insert_left (a : A) (b₁ b₂ : bag A) : insert a b₁ ++ b₂ = insert a (b₁ ++ b₂) :=
quot.induction_on₂ b₁ b₂ (λ l₁ l₂, quot.sound (by rewrite append_cons; apply perm.refl))

lemma append_insert_right (a : A) (b₁ b₂ : bag A) : b₁ ++ insert a b₂ = insert a (b₁ ++ b₂) :=
calc b₁ ++ insert a b₂  = insert a b₂ ++ b₁   : append.comm
                    ... = insert a (b₂ ++ b₁) : append_insert_left
                    ... = insert a (b₁ ++ b₂) : append.comm

protected lemma induction_on [recursor 3] {C : bag A → Prop} (b : bag A) (h₁ : C empty) (h₂ : ∀ a b, C b → C (insert a b)) : C b :=
quot.induction_on b (λ l, list.induction_on l h₁ (λ h t ih, h₂ h ⟦t⟧ ih))

section decidable_eq
variable [decA : decidable_eq A]
include decA
open decidable

definition has_decidable_eq [instance] (b₁ b₂ : bag A) : decidable (b₁ = b₂) :=
quot.rec_on_subsingleton₂ b₁ b₂ (λ l₁ l₂,
  match decidable_perm l₁ l₂ with
  | inl h := inl (quot.sound h)
  | inr h := inr (λ n, absurd (quot.exact n) h)
  end)
end decidable_eq

section count
variable [decA : decidable_eq A]
include decA

definition count (a : A) (b : bag A) : nat :=
quot.lift_on b (λ l, count a l)
  (λ l₁ l₂ h, count_eq_of_perm h a)

lemma count_empty (a : A) : count a empty = 0 :=
rfl

lemma count_insert (a : A) (b : bag A) : count a (insert a b) = succ (count a b) :=
quot.induction_on b (λ l, begin unfold [insert, count], rewrite count_cons_eq end)

lemma count_insert_of_ne {a₁ a₂ : A} (h : a₁ ≠ a₂) (b : bag A) : count a₁ (insert a₂ b) = count a₁ b :=
quot.induction_on b (λ l, begin unfold [insert, count], rewrite (count_cons_of_ne h) end)

lemma count_singleton (a : A) : count a (singleton a) = 1 :=
begin rewrite [-insert_empty_eq_singleton, count_insert] end

lemma count_append (a : A) (b₁ b₂ : bag A) : count a (append b₁ b₂) = count a b₁ + count a b₂ :=
quot.induction_on₂ b₁ b₂ (λ l₁ l₂, begin unfold [append, count], rewrite list.count_append end)

open perm decidable
protected lemma ext {b₁ b₂ : bag A} : (∀ a, count a b₁ = count a b₂) → b₁ = b₂ :=
quot.induction_on₂ b₁ b₂ (λ l₁ l₂ (h : ∀ a, count a ⟦l₁⟧ = count a ⟦l₂⟧),
 have gen : ∀ (l₁ l₂ : list A), (∀ a, list.count a l₁ = list.count a l₂) → l₁ ~ l₂
 | []       []       h₁ := !perm.refl
 | []       (a₂::s₂) h₁ := assert list.count a₂ [] = list.count a₂ (a₂::s₂), from h₁ a₂, by rewrite [count_nil at this, count_cons_eq at this]; contradiction
 | (a::s₁) s₂       h₁ :=
   assert g₁ : list.count a (a::s₁) > 0, from count_gt_zero_of_mem !mem_cons,
   assert list.count a (a::s₁) = list.count a s₂, from h₁ a,
   assert list.count a s₂ > 0, by rewrite [-this]; exact g₁,
   have a ∈ s₂,                from mem_of_count_gt_zero this,
   have ∃ l r, s₂ = l++(a::r), from mem_split this,
   obtain l r (e₁ : s₂ = l++(a::r)), from this,
   have ∀ a, list.count a s₁ = list.count a (l++r), from
     take a₁,
     assert e₂ : list.count a₁ (a::s₁) = list.count a₁ (l++(a::r)), by rewrite -e₁; exact h₁ a₁,
     by_cases
       (suppose a₁ = a, begin
          rewrite [-this at e₂, list.count_append at e₂, *count_cons_eq at e₂, add_succ at e₂],
          injection e₂ with e₃, rewrite e₃,
          rewrite list.count_append
        end)
       (suppose a₁ ≠ a,
        by rewrite [list.count_append at e₂, *count_cons_of_ne this at e₂, e₂, list.count_append]),
   have ih : s₁ ~ l++r,             from gen s₁ (l++r) this,
   calc a::s₁ ~ a::(l++r) : perm.skip a ih
         ...  ~ l++(a::r) : perm_middle
         ...  = s₂        : e₁,
 quot.sound (gen l₁ l₂ h))

definition insert.inj {a : A} {b₁ b₂ : bag A} : insert a b₁ = insert a b₂ → b₁ = b₂ :=
assume h, bag.ext (take x,
  assert e : count x (insert a b₁) = count x (insert a b₂), by rewrite h,
  by_cases
    (suppose x = a, begin subst x, rewrite [*count_insert at e], injection e, assumption end)
    (suppose x ≠ a, begin rewrite [*count_insert_of_ne this at e], assumption end))
end count

section extract
open decidable
variable [decA : decidable_eq A]
include decA

definition extract (a : A) (b : bag A) : bag A :=
quot.lift_on b (λ l, ⟦filter (λ c, c ≠ a) l⟧)
  (λ l₁ l₂ h, quot.sound (perm_filter h))

lemma extract_singleton (a : A) : extract a (singleton a) = empty :=
begin unfold [extract, singleton, of_list, filter], rewrite [if_neg (λ h : a ≠ a, absurd rfl h)] end

lemma extract_insert (a : A) (b : bag A) : extract a (insert a b) = extract a b :=
quot.induction_on b (λ l, begin
  unfold [insert, extract],
  rewrite [@filter_cons_of_neg _ (λ c, c ≠ a) _ _ l (not_not_intro (eq.refl a))]
end)

lemma extract_insert_of_ne {a₁ a₂ : A} (h : a₁ ≠ a₂) (b : bag A) : extract a₁ (insert a₂ b) = insert a₂ (extract a₁ b) :=
quot.induction_on b (λ l, begin
  unfold [insert, extract],
  rewrite [@filter_cons_of_pos _ (λ c, c ≠ a₁) _ _ l (ne.symm h)]
end)

lemma count_extract (a : A) (b : bag A) : count a (extract a b) = 0 :=
bag.induction_on b rfl
  (λ c b ih, by_cases
     (suppose a = c, begin subst c, rewrite [extract_insert, ih] end)
     (suppose a ≠ c, begin rewrite [extract_insert_of_ne this, count_insert_of_ne this, ih] end))

lemma count_extract_of_ne {a₁ a₂ : A} (h : a₁ ≠ a₂) (b : bag A) : count a₁ (extract a₂ b) = count a₁ b :=
bag.induction_on b rfl
  (take x b ih, by_cases
    (suppose x = a₁, begin subst x, rewrite [extract_insert_of_ne (ne.symm h), *count_insert, ih] end)
    (suppose x ≠ a₁, by_cases
      (suppose x = a₂, begin subst x, rewrite [extract_insert, ih, count_insert_of_ne h] end)
      (suppose x ≠ a₂, begin
        rewrite [count_insert_of_ne (ne.symm `x ≠ a₁`), extract_insert_of_ne (ne.symm this)],
        rewrite [count_insert_of_ne (ne.symm `x ≠ a₁`), ih]
       end)))
end extract

section erase
variable [decA : decidable_eq A]
include decA

definition erase (a : A) (b : bag A) : bag A :=
quot.lift_on b (λ l, ⟦erase a l⟧)
  (λ l₁ l₂ h, quot.sound (erase_perm_erase_of_perm _ h))

lemma erase_empty (a : A) : erase a empty = empty :=
rfl

lemma erase_insert (a : A) (b : bag A) : erase a (insert a b) = b :=
quot.induction_on b (λ l, quot.sound (by rewrite erase_cons_head; apply perm.refl))

lemma erase_insert_of_ne {a₁ a₂ : A} (h : a₁ ≠ a₂) (b : bag A) : erase a₁ (insert a₂ b) = insert a₂ (erase a₁ b) :=
quot.induction_on b (λ l, quot.sound (by rewrite (erase_cons_tail _ h); apply perm.refl))

end erase

section member
variable [decA : decidable_eq A]
include decA

definition mem (a : A) (b : bag A) := count a b > 0
infix ∈ := mem

lemma mem_def (a : A) (b : bag A) : (a ∈ b) = (count a b > 0) :=
rfl

lemma mem_insert (a : A) (b : bag A) : a ∈ insert a b :=
begin unfold mem, rewrite count_insert, exact dec_trivial end

lemma mem_of_list_iff_mem (a : A) (l : list A) : a ∈ of_list l ↔ a ∈ l :=
iff.intro !mem_of_count_gt_zero !count_gt_zero_of_mem

lemma count_of_list_eq_count (a : A) (l : list A) : count a (of_list l) = list.count a l :=
rfl
end member

section union_inter
variable [decA : decidable_eq A]
include decA
open perm decidable

private definition union_list (l₁ l₂ : list A) :=
erase_dup (l₁ ++ l₂)

private lemma perm_union_list {l₁ l₂ l₃ l₄ : list A} (h₁ : l₁ ~ l₃) (h₂ : l₂ ~ l₄) : union_list l₁ l₂ ~ union_list l₃ l₄ :=
perm_erase_dup_of_perm (perm_app h₁ h₂)

private lemma nodup_union_list (l₁ l₂ : list A) : nodup (union_list l₁ l₂) :=
!nodup_erase_dup

private definition not_mem_of_not_mem_union_list_left {a : A} {l₁ l₂ : list A} (h : a ∉ union_list l₁ l₂) : a ∉ l₁ :=
suppose a ∈ l₁,
have a ∈ l₁ ++ l₂, from mem_append_left _ this,
have a ∈ erase_dup (l₁ ++ l₂), from mem_erase_dup this,
absurd this h

private definition not_mem_of_not_mem_union_list_right {a : A} {l₁ l₂ : list A} (h : a ∉ union_list l₁ l₂) : a ∉ l₂ :=
suppose a ∈ l₂,
have a ∈ l₁ ++ l₂, from mem_append_right _ this,
have a ∈ erase_dup (l₁ ++ l₂), from mem_erase_dup this,
absurd this h

private definition gen : nat → A → list A
| 0     a := nil
| (n+1) a := a :: gen n a

private lemma not_mem_gen_of_ne {a b : A} (h : a ≠ b) : ∀ n, a ∉ gen n b
| 0     := !not_mem_nil
| (n+1) := not_mem_cons_of_ne_of_not_mem h (not_mem_gen_of_ne n)

private lemma count_gen : ∀ (a : A) (n : nat), list.count a (gen n a) = n
| a 0     := rfl
| a (n+1) := begin unfold gen, rewrite [count_cons_eq, count_gen] end

private lemma count_gen_eq_zero_of_ne {a b : A} (h : a ≠ b) : ∀ n, list.count a (gen n b) = 0
| 0     := rfl
| (n+1) := begin unfold gen, rewrite [count_cons_of_ne h, count_gen_eq_zero_of_ne] end

private definition max_count (l₁ l₂ : list A) : list A → list A
| []     := []
| (a::l) := if list.count a l₁ ≥ list.count a l₂ then gen (list.count a l₁) a ++ max_count l else gen (list.count a l₂) a ++ max_count l

private definition min_count (l₁ l₂ : list A) : list A → list A
| []     := []
| (a::l) := if list.count a l₁ ≤ list.count a l₂ then gen (list.count a l₁) a ++ min_count l else gen (list.count a l₂) a ++ min_count l

private lemma not_mem_max_count_of_not_mem (l₁ l₂ : list A) : ∀ {a l}, a ∉ l → a ∉ max_count l₁ l₂ l
| a []     h := !not_mem_nil
| a (b::l) h :=
  assert ih : a ∉ max_count l₁ l₂ l, from not_mem_max_count_of_not_mem (not_mem_of_not_mem_cons h),
  assert a ≠ b, from ne_of_not_mem_cons h,
  by_cases
    (suppose list.count b l₁ ≥ list.count b l₂, begin
      unfold max_count, rewrite [if_pos this],
      exact not_mem_append (not_mem_gen_of_ne `a ≠ b` _) ih
     end)
    (suppose ¬ list.count b l₁ ≥ list.count b l₂, begin
      unfold max_count, rewrite [if_neg this],
      exact not_mem_append (not_mem_gen_of_ne `a ≠ b` _) ih
     end)

private lemma max_count_eq (l₁ l₂ : list A) : ∀ {a : A} {l : list A}, a ∈ l → nodup l → list.count a (max_count l₁ l₂ l) = max (list.count a l₁) (list.count a l₂)
| a []     h₁ h₂ := absurd h₁ !not_mem_nil
| a (b::l) h₁ h₂ :=
  assert nodup l, from nodup_of_nodup_cons h₂,
  assert b ∉ l,   from not_mem_of_nodup_cons h₂,
  or.elim h₁
  (suppose a = b,
    have a ∉ l, by rewrite this; assumption,
    assert a ∉ max_count l₁ l₂ l, from not_mem_max_count_of_not_mem l₁ l₂ this,
    by_cases
    (suppose i : list.count a l₁ ≥ list.count a l₂, begin
       unfold max_count, subst b,
       rewrite [if_pos i, list.count_append, count_gen, max_eq_left i, count_eq_zero_of_not_mem `a ∉ max_count l₁ l₂ l`]
     end)
    (suppose i : ¬ list.count a l₁ ≥ list.count a l₂, begin
       unfold max_count, subst b,
       rewrite [if_neg i, list.count_append, count_gen, max_eq_right' (lt_of_not_ge i), count_eq_zero_of_not_mem `a ∉ max_count l₁ l₂ l`]
     end))
  (suppose a ∈ l,
    assert a ≠ b, from suppose a = b, by subst b; contradiction,
    assert ih : list.count a (max_count l₁ l₂ l) = max (list.count a l₁) (list.count a l₂), from max_count_eq `a ∈ l` `nodup l`,
    by_cases
    (suppose i : list.count b l₁ ≥ list.count b l₂, begin
       unfold max_count,
       rewrite [if_pos i, -ih, list.count_append, count_gen_eq_zero_of_ne `a ≠ b`, zero_add]
     end)
    (suppose i : ¬ list.count b l₁ ≥ list.count b l₂, begin
       unfold max_count,
       rewrite [if_neg i, -ih, list.count_append, count_gen_eq_zero_of_ne `a ≠ b`, zero_add]
     end))

private lemma not_mem_min_count_of_not_mem (l₁ l₂ : list A) : ∀ {a l}, a ∉ l → a ∉ min_count l₁ l₂ l
| a []     h := !not_mem_nil
| a (b::l) h :=
  assert ih : a ∉ min_count l₁ l₂ l, from not_mem_min_count_of_not_mem (not_mem_of_not_mem_cons h),
  assert a ≠ b, from ne_of_not_mem_cons h,
  by_cases
    (suppose list.count b l₁ ≤ list.count b l₂, begin
      unfold min_count, rewrite [if_pos this],
      exact not_mem_append (not_mem_gen_of_ne `a ≠ b` _) ih
     end)
    (suppose ¬ list.count b l₁ ≤ list.count b l₂, begin
      unfold min_count, rewrite [if_neg this],
      exact not_mem_append (not_mem_gen_of_ne `a ≠ b` _) ih
     end)

private lemma min_count_eq (l₁ l₂ : list A) : ∀ {a : A} {l : list A}, a ∈ l → nodup l → list.count a (min_count l₁ l₂ l) = min (list.count a l₁) (list.count a l₂)
| a []     h₁ h₂ := absurd h₁ !not_mem_nil
| a (b::l) h₁ h₂ :=
  assert nodup l, from nodup_of_nodup_cons h₂,
  assert b ∉ l,   from not_mem_of_nodup_cons h₂,
  or.elim h₁
  (suppose a = b,
    have a ∉ l, by rewrite this; assumption,
    assert a ∉ min_count l₁ l₂ l, from not_mem_min_count_of_not_mem l₁ l₂ this,
    by_cases
    (suppose i : list.count a l₁ ≤ list.count a l₂, begin
       unfold min_count, subst b,
       rewrite [if_pos i, list.count_append, count_gen, min_eq_left i, count_eq_zero_of_not_mem `a ∉ min_count l₁ l₂ l`]
     end)
    (suppose i : ¬ list.count a l₁ ≤ list.count a l₂, begin
       unfold min_count, subst b,
       rewrite [if_neg i, list.count_append, count_gen, min_eq_right (le_of_lt (lt_of_not_ge i)), count_eq_zero_of_not_mem `a ∉ min_count l₁ l₂ l`]
     end))
  (suppose a ∈ l,
    assert a ≠ b, from suppose a = b, by subst b; contradiction,
    assert ih : list.count a (min_count l₁ l₂ l) = min (list.count a l₁) (list.count a l₂), from min_count_eq `a ∈ l` `nodup l`,
    by_cases
    (suppose i : list.count b l₁ ≤ list.count b l₂, begin
       unfold min_count,
       rewrite [if_pos i, -ih, list.count_append, count_gen_eq_zero_of_ne `a ≠ b`, zero_add]
     end)
    (suppose i : ¬ list.count b l₁ ≤ list.count b l₂, begin
       unfold min_count,
       rewrite [if_neg i, -ih, list.count_append, count_gen_eq_zero_of_ne `a ≠ b`, zero_add]
     end))

private lemma perm_max_count_left {l₁ l₂ l₃ l₄ : list A} (h₁ : l₁ ~ l₃) (h₂ : l₂ ~ l₄) : ∀ l, max_count l₁ l₂ l ~ max_count l₃ l₄ l
| []     := by esimp
| (a::l) :=
  assert e₁ : list.count a l₁ = list.count a l₃, from count_eq_of_perm h₁ a,
  assert e₂ : list.count a l₂ = list.count a l₄, from count_eq_of_perm h₂ a,
  by_cases
    (suppose list.count a l₁ ≥ list.count a l₂,
     begin unfold max_count, rewrite [-e₁, -e₂, *if_pos this], exact perm_app !perm.refl !perm_max_count_left end)
    (suppose ¬ list.count a l₁ ≥ list.count a l₂,
     begin unfold max_count, rewrite [-e₁, -e₂, *if_neg this], exact perm_app !perm.refl !perm_max_count_left end)

private lemma perm_app_left_comm (l₁ l₂ l₃ : list A) : l₁ ++ (l₂ ++ l₃) ~ l₂ ++ (l₁ ++ l₃) :=
calc l₁ ++ (l₂ ++ l₃) = (l₁ ++ l₂) ++ l₃ : list.append.assoc
                ...   ~ (l₂ ++ l₁) ++ l₃ : perm_app !perm_app_comm !perm.refl
                ...   = l₂ ++ (l₁ ++ l₃) : list.append.assoc

private lemma perm_max_count_right {l r : list A} (h : l ~ r) : ∀ l₁ l₂, max_count l₁ l₂ l ~ max_count l₁ l₂ r :=
perm.induction_on h
  (λ l₁ l₂, !perm.refl)
  (λ x s₁ s₂ p ih l₁ l₂, by_cases
    (suppose i : list.count x l₁ ≥ list.count x l₂,
      begin unfold max_count, rewrite [*if_pos i], exact perm_app !perm.refl !ih end)
    (suppose i : ¬ list.count x l₁ ≥ list.count x l₂,
      begin unfold max_count, rewrite [*if_neg i], exact perm_app !perm.refl !ih end))
  (λ x y l l₁ l₂, by_cases
    (suppose i₁ : list.count x l₁ ≥ list.count x l₂, by_cases
      (suppose i₂ : list.count y l₁ ≥ list.count y l₂,
        begin unfold max_count, unfold max_count, rewrite [*if_pos i₁, *if_pos i₂], apply perm_app_left_comm end)
      (suppose i₂ : ¬ list.count y l₁ ≥ list.count y l₂,
        begin unfold max_count, unfold max_count, rewrite [*if_pos i₁, *if_neg i₂], apply perm_app_left_comm end))
    (suppose i₁ : ¬ list.count x l₁ ≥ list.count x l₂, by_cases
      (suppose i₂ : list.count y l₁ ≥ list.count y l₂,
        begin unfold max_count, unfold max_count, rewrite [*if_neg i₁, *if_pos i₂], apply perm_app_left_comm end)
      (suppose i₂ : ¬ list.count y l₁ ≥ list.count y l₂,
        begin unfold max_count, unfold max_count, rewrite [*if_neg i₁, *if_neg i₂], apply perm_app_left_comm end)))
  (λ s₁ s₂ s₃ p₁ p₂ ih₁ ih₂ l₁ l₂, perm.trans (ih₁ l₁ l₂) (ih₂ l₁ l₂))

private lemma perm_max_count {l₁ l₂ l₃ r₁ r₂ r₃ : list A} (p₁ : l₁ ~ r₁) (p₂ : l₂ ~ r₂) (p₃ : l₃ ~ r₃) : max_count l₁ l₂ l₃ ~ max_count r₁ r₂ r₃ :=
calc max_count l₁ l₂ l₃ ~ max_count r₁ r₂ l₃ : perm_max_count_left p₁ p₂
                    ... ~ max_count r₁ r₂ r₃ : perm_max_count_right p₃

private lemma perm_min_count_left {l₁ l₂ l₃ l₄ : list A} (h₁ : l₁ ~ l₃) (h₂ : l₂ ~ l₄) : ∀ l, min_count l₁ l₂ l ~ min_count l₃ l₄ l
| []     := by esimp
| (a::l) :=
  assert e₁ : list.count a l₁ = list.count a l₃, from count_eq_of_perm h₁ a,
  assert e₂ : list.count a l₂ = list.count a l₄, from count_eq_of_perm h₂ a,
  by_cases
    (suppose list.count a l₁ ≤ list.count a l₂,
     begin unfold min_count, rewrite [-e₁, -e₂, *if_pos this], exact perm_app !perm.refl !perm_min_count_left end)
    (suppose ¬ list.count a l₁ ≤ list.count a l₂,
     begin unfold min_count, rewrite [-e₁, -e₂, *if_neg this], exact perm_app !perm.refl !perm_min_count_left end)

private lemma perm_min_count_right {l r : list A} (h : l ~ r) : ∀ l₁ l₂, min_count l₁ l₂ l ~ min_count l₁ l₂ r :=
perm.induction_on h
  (λ l₁ l₂, !perm.refl)
  (λ x s₁ s₂ p ih l₁ l₂, by_cases
    (suppose i : list.count x l₁ ≤ list.count x l₂,
      begin unfold min_count, rewrite [*if_pos i], exact perm_app !perm.refl !ih end)
    (suppose i : ¬ list.count x l₁ ≤ list.count x l₂,
      begin unfold min_count, rewrite [*if_neg i], exact perm_app !perm.refl !ih end))
  (λ x y l l₁ l₂, by_cases
    (suppose i₁ : list.count x l₁ ≤ list.count x l₂, by_cases
      (suppose i₂ : list.count y l₁ ≤ list.count y l₂,
        begin unfold min_count, unfold min_count, rewrite [*if_pos i₁, *if_pos i₂], apply perm_app_left_comm end)
      (suppose i₂ : ¬ list.count y l₁ ≤ list.count y l₂,
        begin unfold min_count, unfold min_count, rewrite [*if_pos i₁, *if_neg i₂], apply perm_app_left_comm end))
    (suppose i₁ : ¬ list.count x l₁ ≤ list.count x l₂, by_cases
      (suppose i₂ : list.count y l₁ ≤ list.count y l₂,
        begin unfold min_count, unfold min_count, rewrite [*if_neg i₁, *if_pos i₂], apply perm_app_left_comm end)
      (suppose i₂ : ¬ list.count y l₁ ≤ list.count y l₂,
        begin unfold min_count, unfold min_count, rewrite [*if_neg i₁, *if_neg i₂], apply perm_app_left_comm end)))
  (λ s₁ s₂ s₃ p₁ p₂ ih₁ ih₂ l₁ l₂, perm.trans (ih₁ l₁ l₂) (ih₂ l₁ l₂))

private lemma perm_min_count {l₁ l₂ l₃ r₁ r₂ r₃ : list A} (p₁ : l₁ ~ r₁) (p₂ : l₂ ~ r₂) (p₃ : l₃ ~ r₃) : min_count l₁ l₂ l₃ ~ min_count r₁ r₂ r₃ :=
calc min_count l₁ l₂ l₃ ~ min_count r₁ r₂ l₃ : perm_min_count_left p₁ p₂
                    ... ~ min_count r₁ r₂ r₃ : perm_min_count_right p₃

definition union (b₁ b₂ : bag A) : bag A :=
quot.lift_on₂ b₁ b₂ (λ l₁ l₂, ⟦max_count l₁ l₂ (union_list l₁ l₂)⟧)
  (λ l₁ l₂ l₃ l₄ p₁ p₂, quot.sound (perm_max_count p₁ p₂ (perm_union_list p₁ p₂)))
infix ∪ := union

definition inter (b₁ b₂ : bag A) : bag A :=
quot.lift_on₂ b₁ b₂ (λ l₁ l₂, ⟦min_count l₁ l₂ (union_list l₁ l₂)⟧)
  (λ l₁ l₂ l₃ l₄ p₁ p₂, quot.sound (perm_min_count p₁ p₂ (perm_union_list p₁ p₂)))
infix ∩ := inter

lemma count_union (a : A) (b₁ b₂ : bag A) : count a (b₁ ∪ b₂) = max (count a b₁) (count a b₂) :=
quot.induction_on₂ b₁ b₂ (λ l₁ l₂, by_cases
  (suppose a ∈ union_list l₁ l₂, !max_count_eq this !nodup_union_list)
  (suppose ¬ a ∈ union_list l₁ l₂,
    assert ¬ a ∈ l₁, from not_mem_of_not_mem_union_list_left `¬ a ∈ union_list l₁ l₂`,
    assert ¬ a ∈ l₂, from not_mem_of_not_mem_union_list_right `¬ a ∈ union_list l₁ l₂`,
    assert n : ¬ a ∈ max_count l₁ l₂ (union_list l₁ l₂), from not_mem_max_count_of_not_mem l₁ l₂ `¬ a ∈ union_list l₁ l₂`,
    begin
      unfold [union, count],
      rewrite [count_eq_zero_of_not_mem `¬ a ∈ l₁`, count_eq_zero_of_not_mem `¬ a ∈ l₂`, max_self],
      rewrite [count_eq_zero_of_not_mem n]
    end))

lemma count_inter (a : A) (b₁ b₂ : bag A) : count a (b₁ ∩ b₂) = min (count a b₁) (count a b₂) :=
quot.induction_on₂ b₁ b₂ (λ l₁ l₂, by_cases
  (suppose a ∈ union_list l₁ l₂, !min_count_eq this !nodup_union_list)
  (suppose ¬ a ∈ union_list l₁ l₂,
    assert ¬ a ∈ l₁, from not_mem_of_not_mem_union_list_left `¬ a ∈ union_list l₁ l₂`,
    assert ¬ a ∈ l₂, from not_mem_of_not_mem_union_list_right `¬ a ∈ union_list l₁ l₂`,
    assert n : ¬ a ∈ min_count l₁ l₂ (union_list l₁ l₂), from not_mem_min_count_of_not_mem l₁ l₂ `¬ a ∈ union_list l₁ l₂`,
    begin
      unfold [inter, count],
      rewrite [count_eq_zero_of_not_mem `¬ a ∈ l₁`, count_eq_zero_of_not_mem `¬ a ∈ l₂`, min_self],
      rewrite [count_eq_zero_of_not_mem n]
    end))

lemma union.comm (b₁ b₂ : bag A) : b₁ ∪ b₂ = b₂ ∪ b₁ :=
bag.ext (λ a, by rewrite [*count_union, max.comm])

lemma union.assoc (b₁ b₂ b₃ : bag A) : (b₁ ∪ b₂) ∪ b₃ = b₁ ∪ (b₂ ∪ b₃) :=
bag.ext (λ a, by rewrite [*count_union, max.assoc])

theorem union.left_comm (s₁ s₂ s₃ : bag A) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
!left_comm union.comm union.assoc s₁ s₂ s₃

lemma union_self (b : bag A) : b ∪ b = b :=
bag.ext (λ a, by rewrite [*count_union, max_self])

lemma union_empty (b : bag A) : b ∪ empty = b :=
bag.ext (λ a, by rewrite [*count_union, count_empty, max_zero])

lemma empty_union (b : bag A) : empty ∪ b = b :=
calc empty ∪ b = b ∪ empty : union.comm
           ... = b         : union_empty

lemma inter.comm (b₁ b₂ : bag A) : b₁ ∩ b₂ = b₂ ∩ b₁ :=
bag.ext (λ a, by rewrite [*count_inter, min.comm])

lemma inter.assoc (b₁ b₂ b₃ : bag A) : (b₁ ∩ b₂) ∩ b₃ = b₁ ∩ (b₂ ∩ b₃) :=
bag.ext (λ a, by rewrite [*count_inter, min.assoc])

theorem inter.left_comm (s₁ s₂ s₃ : bag A) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
!left_comm inter.comm inter.assoc s₁ s₂ s₃

lemma inter_self (b : bag A) : b ∩ b = b :=
bag.ext (λ a, by rewrite [*count_inter, min_self])

lemma inter_empty (b : bag A) : b ∩ empty = empty :=
bag.ext (λ a, by rewrite [*count_inter, count_empty, min_zero])

lemma empty_inter (b : bag A) : empty ∩ b = empty :=
calc empty ∩ b = b ∩ empty : inter.comm
           ... = empty     : inter_empty

lemma append_union_inter (b₁ b₂ : bag A) : (b₁ ∪ b₂) ++ (b₁ ∩ b₂) = b₁ ++ b₂ :=
bag.ext (λ a, begin
  rewrite [*count_append, count_inter, count_union], unfold [max, min],
  apply (@by_cases (count a b₁ < count a b₂)),
  { intro H, rewrite [*if_pos H, add.comm] },
  { intro H, rewrite [*if_neg H, add.comm] }
end)

lemma inter.left_distrib (b₁ b₂ b₃ : bag A) : b₁ ∩ (b₂ ∪ b₃) = (b₁ ∩ b₂) ∪ (b₁ ∩ b₃) :=
bag.ext (λ a, begin
  rewrite [*count_inter, *count_union, *count_inter],
  apply (@by_cases (count a b₁ ≤ count a b₂)),
  { intro H₁₂, apply (@by_cases (count a b₂ ≤ count a b₃)),
    { intro H₂₃,
      have H₁₃ : count a b₁ ≤ count a b₃, from le.trans H₁₂ H₂₃,
      rewrite [max_eq_right H₂₃, min_eq_left H₁₂, min_eq_left H₁₃, max_self]},
    { intro H₂₃,
      rewrite [min_eq_left H₁₂, max.comm, max_eq_right' (lt_of_not_ge H₂₃) ],
      apply (@by_cases (count a b₁ ≤ count a b₃)),
      { intro H₁₃, rewrite [min_eq_left H₁₃, max_self, min_eq_left H₁₂] },
      { intro H₁₃,
        rewrite [min.comm (count a b₁) (count a b₃), min_eq_left' (lt_of_not_ge H₁₃),
                 min_eq_left H₁₂, max.comm, max_eq_right' (lt_of_not_ge H₁₃)]}}},
  { intro H₁₂, apply (@by_cases (count a b₂ ≤ count a b₃)),
    { intro H₂₃,
      rewrite [max_eq_right H₂₃],
      apply (@by_cases (count a b₁ ≤ count a b₃)),
      { intro H₁₃, rewrite [min_eq_left H₁₃, min.comm, min_eq_left' (lt_of_not_ge H₁₂), max_eq_right' (lt_of_not_ge H₁₂)] },
      { intro H₁₃, rewrite [min.comm, min_eq_left' (lt_of_not_ge H₁₃), min.comm, min_eq_left' (lt_of_not_ge H₁₂), max_eq_right H₂₃] } },
    { intro H₂₃,
      have H₁₃ : count a b₁ > count a b₃, from lt.trans (lt_of_not_ge H₂₃) (lt_of_not_ge H₁₂),
      rewrite [max.comm, max_eq_right' (lt_of_not_ge H₂₃), min.comm, min_eq_left' (lt_of_not_ge H₁₂)],
      rewrite [min.comm, min_eq_left' H₁₃, max.comm, max_eq_right' (lt_of_not_ge H₂₃)] } }
end)

lemma inter.right_distrib (b₁ b₂ b₃ : bag A) : (b₁ ∪ b₂) ∩ b₃ = (b₁ ∩ b₃) ∪ (b₂ ∩ b₃) :=
calc (b₁ ∪ b₂) ∩ b₃ = b₃ ∩ (b₁ ∪ b₂)        : inter.comm
              ...   = (b₃ ∩ b₁) ∪ (b₃ ∩ b₂) : inter.left_distrib
              ...   = (b₁ ∩ b₃) ∪ (b₃ ∩ b₂) : inter.comm
              ...   = (b₁ ∩ b₃) ∪ (b₂ ∩ b₃) : inter.comm
end union_inter

section subbag
variable [decA : decidable_eq A]
include decA

definition subbag (b₁ b₂ : bag A) := ∀ a, count a b₁ ≤ count a b₂

infix ⊆ := subbag

lemma subbag.refl (b : bag A) : b ⊆ b :=
take a, !le.refl

lemma subbag.trans {b₁ b₂ b₃ : bag A} : b₁ ⊆ b₂ → b₂ ⊆ b₃ → b₁ ⊆ b₃ :=
assume h₁ h₂, take a, le.trans (h₁ a) (h₂ a)

lemma subbag.antisymm {b₁ b₂ : bag A} : b₁ ⊆ b₂ → b₂ ⊆ b₁ → b₁ = b₂ :=
assume h₁ h₂, bag.ext (take a, le.antisymm (h₁ a) (h₂ a))

lemma count_le_of_subbag {b₁ b₂ : bag A} : b₁ ⊆ b₂ → ∀ a, count a b₁ ≤ count a b₂ :=
assume h, h

lemma subbag.intro {b₁ b₂ : bag A} : (∀ a, count a b₁ ≤ count a b₂) → b₁ ⊆ b₂ :=
assume h, h

lemma empty_subbag (b : bag A) : empty ⊆ b :=
subbag.intro (take a, !zero_le)

lemma eq_empty_of_subbag_empty {b : bag A} : b ⊆ empty → b = empty :=
assume h, subbag.antisymm h (empty_subbag b)

lemma union_subbag_of_subbag_of_subbag {b₁ b₂ b₃ : bag A} : b₁ ⊆ b₃ → b₂ ⊆ b₃ → b₁ ∪ b₂ ⊆ b₃ :=
assume h₁ h₂, subbag.intro (λ a, calc
  count a (b₁ ∪ b₂) = max (count a b₁) (count a b₂) : by rewrite count_union
                ... ≤ count a b₃                    : max_le (h₁ a) (h₂ a))

lemma subbag_inter_of_subbag_of_subbag {b₁ b₂ b₃ : bag A} : b₁ ⊆ b₂ → b₁ ⊆ b₃ → b₁ ⊆ b₂ ∩ b₃ :=
assume h₁ h₂, subbag.intro (λ a, calc
  count a b₁ ≤ min (count a b₂) (count a b₃) : le_min (h₁ a) (h₂ a)
         ... = count a (b₂ ∩ b₃)             : by rewrite count_inter)

lemma subbag_union_left (b₁ b₂ : bag A) : b₁ ⊆ b₁ ∪ b₂ :=
subbag.intro (take a, by rewrite [count_union]; apply le_max_left)

lemma subbag_union_right (b₁ b₂ : bag A) : b₂ ⊆ b₁ ∪ b₂ :=
subbag.intro (take a, by rewrite [count_union]; apply le_max_right)

lemma inter_subbag_left (b₁ b₂ : bag A) : b₁ ∩ b₂ ⊆ b₁ :=
subbag.intro (take a, by rewrite [count_inter]; apply min_le_left)

lemma inter_subbag_right (b₁ b₂ : bag A) : b₁ ∩ b₂ ⊆ b₂ :=
subbag.intro (take a, by rewrite [count_inter]; apply min_le_right)

lemma subbag_append_left (b₁ b₂ : bag A) : b₁ ⊆ b₁ ++ b₂ :=
subbag.intro (take a, by rewrite [count_append]; apply le_add_right)

lemma subbag_append_right (b₁ b₂ : bag A) : b₂ ⊆ b₁ ++ b₂ :=
subbag.intro (take a, by rewrite [count_append]; apply le_add_left)

lemma inter_subbag_union (b₁ b₂ : bag A) : b₁ ∩ b₂ ⊆ b₁ ∪ b₂ :=
subbag.trans (inter_subbag_left b₁ b₂) (subbag_union_left b₁ b₂)

open decidable

lemma union_subbag_append (b₁ b₂ : bag A) : b₁ ∪ b₂ ⊆ b₁ ++ b₂ :=
subbag.intro (take a, begin
  rewrite [count_append, count_union], unfold max,
  exact by_cases
   (suppose count a b₁ < count a b₂,   by rewrite [if_pos this]; apply le_add_left)
   (suppose ¬ count a b₁ < count a b₂, by rewrite [if_neg this]; apply le_add_right)
end)

lemma subbag_insert (a : A) (b : bag A) : b ⊆ insert a b :=
subbag.intro (take x, by_cases
  (suppose x = a, by rewrite [this, count_insert]; apply le_succ)
  (suppose x ≠ a, by rewrite [count_insert_of_ne this]))

lemma mem_of_subbag_of_mem {a : A} {b₁ b₂ : bag A} : b₁ ⊆ b₂ → a ∈ b₁ → a ∈ b₂ :=
assume h₁ h₂,
have count a b₁ ≤ count a b₂, from count_le_of_subbag h₁ a,
have count a b₁ > 0,          from h₂,
show count a b₂ > 0,          from lt_of_lt_of_le `0 < count a b₁` `count a b₁ ≤ count a b₂`

lemma extract_subbag (a : A) (b : bag A) : extract a b ⊆ b :=
subbag.intro (take x, by_cases
  (suppose x = a, by rewrite [this, count_extract]; apply zero_le)
  (suppose x ≠ a, by rewrite [count_extract_of_ne this]))

open bool

private definition subcount : list A → list A → bool
| []      l₂ := tt
| (a::l₁) l₂ := if list.count a (a::l₁) ≤ list.count a l₂ then subcount l₁ l₂ else ff

private lemma all_of_subcount_eq_tt : ∀ {l₁ l₂ : list A}, subcount l₁ l₂ = tt → ∀ a, list.count a l₁ ≤ list.count a l₂
| []      l₂ h := take x, !zero_le
| (a::l₁) l₂ h := take x,
  have subcount l₁ l₂ = tt, from by_contradiction (suppose subcount l₁ l₂ ≠ tt,
    assert subcount l₁ l₂ = ff, from eq_ff_of_ne_tt this,
    begin unfold subcount at h, rewrite [this at h, if_t_t at h], contradiction end),
  assert ih : ∀ a, list.count a l₁ ≤ list.count a l₂, from all_of_subcount_eq_tt this,
  assert i  : list.count a (a::l₁) ≤ list.count a l₂, from by_contradiction (suppose ¬ list.count a (a::l₁) ≤ list.count a l₂,
    begin unfold subcount at h, rewrite [if_neg this at h], contradiction end),
  by_cases
    (suppose x = a, by rewrite this; apply i)
    (suppose x ≠ a, by rewrite [list.count_cons_of_ne this]; apply ih)

private lemma ex_of_subcount_eq_ff : ∀ {l₁ l₂ : list A}, subcount l₁ l₂ = ff → ∃ a, ¬ list.count a l₁ ≤ list.count a l₂
| []     l₂ h := by contradiction
| (a::l₁) l₂ h := by_cases
  (suppose i : list.count a (a::l₁) ≤ list.count a l₂,
    have subcount l₁ l₂ = ff, from by_contradiction (suppose subcount l₁ l₂ ≠ ff,
      assert subcount l₁ l₂ = tt, from eq_tt_of_ne_ff this,
      begin
        unfold subcount at h,
        rewrite [if_pos i at h, this at h],
        contradiction
      end),
    have ih : ∃ a, ¬ list.count a l₁ ≤ list.count a l₂, from ex_of_subcount_eq_ff this,
    obtain w hw, from ih, by_cases
     (suppose w = a, begin subst w, existsi a, rewrite list.count_cons_eq, apply not_lt_of_ge, apply le_of_lt (lt_of_not_ge hw) end)
     (suppose w ≠ a, exists.intro w (by rewrite (list.count_cons_of_ne `w ≠ a`); exact hw)))
  (suppose ¬ list.count a (a::l₁) ≤ list.count a l₂, exists.intro a this)

definition decidable_subbag [instance] (b₁ b₂ : bag A) : decidable (b₁ ⊆ b₂) :=
quot.rec_on_subsingleton₂ b₁ b₂ (λ l₁ l₂,
  match subcount l₁ l₂ with
  | tt := suppose subcount l₁ l₂ = tt, inl (all_of_subcount_eq_tt this)
  | ff := suppose subcount l₁ l₂ = ff, inr (suppose h : (∀ a, list.count a l₁ ≤ list.count a l₂),
            obtain w hw, from ex_of_subcount_eq_ff `subcount l₁ l₂ = ff`,
            absurd (h w) hw)
  end rfl)
end subbag
end bag
