/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

Set-like operations on lists.
-/

universe variables uu vv
variables {α : Type uu} {β : Type vv}

namespace list

/- disjoint -/
section disjoint

def disjoint (l₁ l₂ : list α) : Prop := ∀ ⦃a⦄, (a ∈ l₁ → a ∈ l₂ → false)

lemma disjoint_left {l₁ l₂ : list α} : disjoint l₁ l₂ → ∀ {a}, a ∈ l₁ → a ∉ l₂ :=
λ d, d

lemma disjoint_right {l₁ l₂ : list α} : disjoint l₁ l₂ → ∀ {a}, a ∈ l₂ → a ∉ l₁ :=
λ d a i₂ i₁, d i₁ i₂

lemma disjoint.comm {l₁ l₂ : list α} : disjoint l₁ l₂ → disjoint l₂ l₁ :=
λ d a i₂ i₁, d i₁ i₂

lemma disjoint_of_subset_left {l₁ l₂ l : list α} : list.subset l₁ l → disjoint l l₂ → disjoint l₁ l₂ :=
λ ss d x xinl₁, d (ss xinl₁)

lemma disjoint_of_subset_right {l₁ l₂ l : list α} : list.subset l₂ l → disjoint l₁ l → disjoint l₁ l₂ :=
λ ss d x xinl xinl₁, d xinl (ss xinl₁)

lemma disjoint_of_disjoint_cons_left {a : α} {l₁ l₂} : disjoint (a::l₁) l₂ → disjoint l₁ l₂ :=
disjoint_of_subset_left (list.subset_cons _ _)

lemma disjoint_of_disjoint_cons_right {a : α} {l₁ l₂} : disjoint l₁ (a::l₂) → disjoint l₁ l₂ :=
disjoint_of_subset_right (list.subset_cons _ _)

lemma disjoint_nil_left (l : list α) : disjoint [] l :=
λ a ab, absurd ab (not_mem_nil a)

lemma disjoint_nil_right (l : list α) : disjoint l [] :=
disjoint.comm (disjoint_nil_left l)

lemma disjoint_cons_of_not_mem_of_disjoint {a : α} {l₁ l₂ : list α} :
  a ∉ l₂ → disjoint l₁ l₂ → disjoint (a::l₁) l₂ :=
λ nainl₂ d x (xinal₁ : x ∈ a::l₁),
  or.elim (eq_or_mem_of_mem_cons xinal₁)
    (λ xeqa  : x = a, eq.symm xeqa ▸ nainl₂)
    (λ xinl₁ : x ∈ l₁, disjoint_left d xinl₁)

lemma disjoint_append_of_disjoint_left {l₁ l₂ l : list α} :
  disjoint l₁ l → disjoint l₂ l → disjoint (l₁++l₂) l :=
λ d₁ d₂ x h, or.elim (mem_or_mem_of_mem_append h) (@d₁ x) (@d₂ x)

lemma disjoint_of_disjoint_append_left_left {l₁ l₂ l : list α} : disjoint (l₁++l₂) l → disjoint l₁ l :=
disjoint_of_subset_left (list.subset_append_left _ _)

lemma disjoint_of_disjoint_append_left_right {l₁ l₂ l : list α} : disjoint (l₁++l₂) l → disjoint l₂ l :=
disjoint_of_subset_left (list.subset_append_right _ _)

lemma disjoint_of_disjoint_append_right_left {l₁ l₂ l : list α} : disjoint l (l₁++l₂) → disjoint l l₁ :=
disjoint_of_subset_right (list.subset_append_left _ _)

lemma disjoint_of_disjoint_append_right_right {l₁ l₂ l : list α} : disjoint l (l₁++l₂) → disjoint l l₂ :=
disjoint_of_subset_right (list.subset_append_right _ _)

end disjoint

/- no duplicates predicate -/

inductive nodup {α : Type uu} : list α → Prop
| ndnil  : nodup []
| ndcons : ∀ {a : α} {l : list α}, a ∉ l → nodup l → nodup (a::l)

section nodup
open nodup

theorem nodup_nil : @nodup α [] :=
ndnil

theorem nodup_cons {a : α} {l : list α} : a ∉ l → nodup l → nodup (a::l)  :=
λ i n, ndcons i n

theorem nodup_singleton (a : α) : nodup [a] :=
nodup_cons (not_mem_nil a) nodup_nil

theorem nodup_of_nodup_cons : ∀ {a : α} {l : list α}, nodup (a::l) → nodup l
| a xs (ndcons i n) := n

theorem not_mem_of_nodup_cons : ∀ {a : α} {l : list α}, nodup (a::l) → a ∉ l
| a xs (ndcons i n) := i

theorem not_nodup_cons_of_mem {a : α} {l : list α} : a ∈ l → ¬ nodup (a :: l) :=
λ ainl d, absurd ainl (not_mem_of_nodup_cons d)

theorem nodup_of_sublist : Π {l₁ l₂ : list α}, l₁ <+ l₂ → nodup l₂ → nodup l₁
| ._ ._ sublist.slnil h := h
| ._ ._ (sublist.cons l₁ l₂ a s) (ndcons i n) := nodup_of_sublist s n
| ._ ._ (sublist.cons2 l₁ l₂ a s) (ndcons i n) :=
  ndcons (λh, i (subset_of_sublist s h)) (nodup_of_sublist s n)

theorem not_nodup_cons_of_not_nodup {a : α} {l : list α} : ¬ nodup l → ¬ nodup (a :: l) :=
contrapos nodup_of_nodup_cons

theorem nodup_of_nodup_append_left {l₁ l₂ : list α} : nodup (l₁++l₂) → nodup l₁ :=
nodup_of_sublist (sublist_append_left l₁ l₂)

theorem nodup_of_nodup_append_right : ∀ {l₁ l₂ : list α}, nodup (l₁++l₂) → nodup l₂
| []      l₂ n := n
| (x::xs) l₂ n := nodup_of_nodup_append_right (nodup_of_nodup_cons n)

theorem disjoint_of_nodup_append : ∀ {l₁ l₂ : list α}, nodup (l₁++l₂) → disjoint l₁ l₂
| []      l₂  d := disjoint_nil_left l₂
| (x::xs) l₂  d :=
  have nodup (x::(xs++l₂)),    from d,
  have x ∉ xs++l₂,             from not_mem_of_nodup_cons this,
  have nxinl₂ : x ∉ l₂,        from not_mem_of_not_mem_append_right this,
  take a, suppose a ∈ x::xs,
    or.elim (eq_or_mem_of_mem_cons this)
      (suppose a = x, eq.symm this ▸ nxinl₂)
      (suppose ainxs : a ∈ xs,
        have nodup (x::(xs++l₂)), from d,
        have nodup (xs++l₂),      from nodup_of_nodup_cons this,
        have disjoint xs l₂,      from disjoint_of_nodup_append this,
        disjoint_left this ainxs)

theorem nodup_append_of_nodup_of_nodup_of_disjoint :
  ∀ {l₁ l₂ : list α}, nodup l₁ → nodup l₂ → disjoint l₁ l₂ → nodup (l₁++l₂)
| []      l₂ d₁ d₂ dsj := begin rw [nil_append], exact d₂ end
| (x::xs) l₂ d₁ d₂ dsj :=
  have ndxs     : nodup xs,            from nodup_of_nodup_cons d₁,
  have disjoint xs l₂,                 from disjoint_of_disjoint_cons_left dsj,
  have ndxsl₂   : nodup (xs++l₂),      from nodup_append_of_nodup_of_nodup_of_disjoint ndxs d₂ this,
  have nxinxs   : x ∉ xs,              from not_mem_of_nodup_cons d₁,
  have x ∉ l₂,                         from disjoint_left dsj (mem_cons_self x xs),
  have x ∉ xs++l₂,                     from not_mem_append nxinxs this,
  nodup_cons this ndxsl₂

theorem nodup_app_comm {l₁ l₂ : list α} (d : nodup (l₁++l₂)) : nodup (l₂++l₁) :=
have d₁  : nodup l₁,       from nodup_of_nodup_append_left d,
have d₂  : nodup l₂,       from nodup_of_nodup_append_right d,
have dsj : disjoint l₁ l₂, from disjoint_of_nodup_append d,
nodup_append_of_nodup_of_nodup_of_disjoint d₂ d₁ (disjoint.comm dsj)

theorem nodup_head {a : α} {l₁ l₂ : list α} (d : nodup (l₁++(a::l₂))) : nodup (a::(l₁++l₂)) :=
have d₁    : nodup (a::(l₂++l₁)), from nodup_app_comm d,
have d₂    : nodup (l₂++l₁),      from nodup_of_nodup_cons d₁,
have d₃    : nodup (l₁++l₂),      from nodup_app_comm d₂,
have nain  : a ∉ l₂++l₁,          from not_mem_of_nodup_cons d₁,
have nain₂ : a ∉ l₂,              from not_mem_of_not_mem_append_left nain,
have nain₁ : a ∉ l₁,              from not_mem_of_not_mem_append_right nain,
nodup_cons (not_mem_append nain₁ nain₂) d₃

theorem nodup_middle {a : α} {l₁ l₂ : list α} (d : nodup (a::(l₁++l₂))) : nodup (l₁++(a::l₂)) :=
have d₁    : nodup (l₁++l₂),      from nodup_of_nodup_cons d,
have nain  : a ∉ l₁++l₂,          from not_mem_of_nodup_cons d,
have disj  : disjoint l₁ l₂,      from disjoint_of_nodup_append d₁,
have d₂    : nodup l₁,            from nodup_of_nodup_append_left d₁,
have d₃    : nodup l₂,            from nodup_of_nodup_append_right d₁,
have nain₂ : a ∉ l₂,              from not_mem_of_not_mem_append_right nain,
have nain₁ : a ∉ l₁,              from not_mem_of_not_mem_append_left nain,
have d₄    : nodup (a::l₂),       from nodup_cons nain₂ d₃,
have disj₂ : disjoint l₁ (a::l₂), from disjoint.comm (disjoint_cons_of_not_mem_of_disjoint nain₁
                                           (disjoint.comm disj)),
nodup_append_of_nodup_of_nodup_of_disjoint d₂ d₄ disj₂

end nodup

end list
