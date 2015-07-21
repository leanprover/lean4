/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Set-like operations on lists
-/
import data.list.basic data.list.comb
open nat function decidable helper_tactics eq.ops

namespace list
section erase
variable {A : Type}
variable [H : decidable_eq A]
include H

definition erase (a : A) : list A → list A
| []     := []
| (b::l) :=
  match H a b with
  | inl e := l
  | inr n := b :: erase l
  end

lemma erase_nil (a : A) : erase a [] = [] :=
rfl

lemma erase_cons_head (a : A) (l : list A) : erase a (a :: l) = l :=
show match H a a with | inl e := l | inr n := a :: erase a l end = l,
by rewrite decidable_eq_inl_refl

lemma erase_cons_tail {a b : A} (l : list A) : a ≠ b → erase a (b::l) = b :: erase a l :=
assume h : a ≠ b,
show match H a b with | inl e := l | inr n₁ := b :: erase a l end = b :: erase a l,
by rewrite (decidable_eq_inr_neg h)

lemma length_erase_of_mem {a : A} : ∀ {l}, a ∈ l → length (erase a l) = pred (length l)
| []         h := rfl
| [x]        h := by rewrite [mem_singleton h, erase_cons_head]
| (x::y::xs) h :=
  by_cases
   (suppose a = x, by rewrite [this, erase_cons_head])
   (suppose a ≠ x,
    assert ainyxs : a ∈ y::xs, from or_resolve_right h this,
    by rewrite [erase_cons_tail _ this, *length_cons, length_erase_of_mem ainyxs])

lemma length_erase_of_not_mem {a : A} : ∀ {l}, a ∉ l → length (erase a l) = length l
| []      h   := rfl
| (x::xs) h   :=
  assert anex   : a ≠ x,  from λ aeqx  : a = x,  absurd (or.inl aeqx) h,
  assert aninxs : a ∉ xs, from λ ainxs : a ∈ xs, absurd (or.inr ainxs) h,
  by rewrite [erase_cons_tail _ anex, length_cons, length_erase_of_not_mem aninxs]

lemma erase_append_left {a : A} : ∀ {l₁} (l₂), a ∈ l₁ → erase a (l₁++l₂) = erase a l₁ ++ l₂
| []      l₂  h := absurd h !not_mem_nil
| (x::xs) l₂  h :=
  by_cases
   (λ aeqx : a = x, by rewrite [aeqx, append_cons, *erase_cons_head])
   (λ anex : a ≠ x,
    assert ainxs : a ∈ xs, from mem_of_ne_of_mem anex h,
    by rewrite [append_cons, *erase_cons_tail _ anex, erase_append_left l₂ ainxs])

lemma erase_append_right {a : A} : ∀ {l₁} (l₂), a ∉ l₁ → erase a (l₁++l₂) = l₁ ++ erase a l₂
| []      l₂ h := rfl
| (x::xs) l₂ h :=
  by_cases
   (λ aeqx : a = x, by rewrite aeqx at h; exact (absurd !mem_cons h))
   (λ anex : a ≠ x,
    assert nainxs : a ∉ xs, from not_mem_of_not_mem_cons h,
    by rewrite [append_cons, *erase_cons_tail _ anex, erase_append_right l₂ nainxs])

lemma erase_sub (a : A) : ∀ l, erase a l ⊆ l
| []      := λ x xine, xine
| (x::xs) := λ y xine,
  by_cases
    (λ aeqx : a = x, by rewrite [aeqx at xine, erase_cons_head at xine]; exact (or.inr xine))
    (λ anex : a ≠ x,
      assert yinxe : y ∈ x :: erase a xs, by rewrite [erase_cons_tail _ anex at xine]; exact xine,
      assert subxs : erase a xs ⊆ xs, from erase_sub xs,
      by_cases
        (λ yeqx : y = x, by rewrite yeqx; apply mem_cons)
        (λ ynex : y ≠ x,
          assert yine  : y ∈ erase a xs, from mem_of_ne_of_mem ynex yinxe,
          assert yinxs : y ∈ xs, from subxs yine,
          or.inr yinxs))

theorem mem_erase_of_ne_of_mem {a b : A} : ∀ {l : list A}, a ≠ b → a ∈ l → a ∈ erase b l
| []     n  i := absurd i !not_mem_nil
| (c::l) n  i := by_cases
  (λ beqc : b = c,
   assert ainl : a ∈ l, from or.elim (eq_or_mem_of_mem_cons i)
     (λ aeqc : a = c, absurd aeqc (beqc ▸ n))
     (λ ainl : a ∈ l, ainl),
   by rewrite [beqc, erase_cons_head]; exact ainl)
  (λ bnec : b ≠ c, by_cases
    (λ aeqc : a = c,
      assert aux : a ∈ c :: erase b l, by rewrite [aeqc]; exact !mem_cons,
      by rewrite [erase_cons_tail _ bnec]; exact aux)
    (λ anec : a ≠ c,
      have ainl  : a ∈ l, from mem_of_ne_of_mem anec i,
      have ainel : a ∈ erase b l, from mem_erase_of_ne_of_mem n ainl,
      assert aux : a ∈ c :: erase b l, from mem_cons_of_mem _ ainel,
      by rewrite [erase_cons_tail _ bnec]; exact aux)) --

theorem mem_of_mem_erase {a b : A} : ∀ {l}, a ∈ erase b l → a ∈ l
| []     i := absurd i !not_mem_nil
| (c::l) i := by_cases
  (λ beqc : b = c, by rewrite [beqc at i, erase_cons_head at i]; exact (mem_cons_of_mem _ i))
  (λ bnec : b ≠ c,
    have i₁ : a ∈ c :: erase b l, by rewrite [erase_cons_tail _ bnec at i]; exact i,
    or.elim (eq_or_mem_of_mem_cons i₁)
      (λ aeqc  : a = c, by rewrite [aeqc]; exact !mem_cons)
      (λ ainel : a ∈ erase b l,
        have ainl : a ∈ l, from mem_of_mem_erase ainel,
        mem_cons_of_mem _ ainl))

theorem all_erase_of_all {p : A → Prop} (a : A) : ∀ {l}, all l p → all (erase a l) p
| []     h := by rewrite [erase_nil]; exact h
| (b::l) h :=
  assert h₁ : all l p, from all_of_all_cons h,
  have   h₂ : all (erase a l) p, from all_erase_of_all h₁,
  have   pb : p b, from of_all_cons h,
  assert h₃ : all (b :: erase a l) p, from all_cons_of_all pb h₂,
  by_cases
    (λ aeqb : a = b, by rewrite [aeqb, erase_cons_head]; exact h₁)
    (λ aneb : a ≠ b, by rewrite [erase_cons_tail _ aneb]; exact h₃)
end erase

/- disjoint -/
section disjoint
variable {A : Type}

definition disjoint (l₁ l₂ : list A) : Prop := ∀ ⦃a⦄, (a ∈ l₁ → a ∈ l₂ → false)

lemma disjoint_left {l₁ l₂ : list A} : disjoint l₁ l₂ → ∀ {a}, a ∈ l₁ → a ∉ l₂ :=
λ d a, d a

lemma disjoint_right {l₁ l₂ : list A} : disjoint l₁ l₂ → ∀ {a}, a ∈ l₂ → a ∉ l₁ :=
λ d a i₂ i₁, d a i₁ i₂

lemma disjoint.comm {l₁ l₂ : list A} : disjoint l₁ l₂ → disjoint l₂ l₁ :=
λ d a i₂ i₁, d a i₁ i₂

lemma disjoint_of_disjoint_cons_left {a : A} {l₁ l₂} : disjoint (a::l₁) l₂ → disjoint l₁ l₂ :=
λ d x xinl₁, disjoint_left d (or.inr xinl₁)

lemma disjoint_of_disjoint_cons_right {a : A} {l₁ l₂} : disjoint l₁ (a::l₂) → disjoint l₁ l₂ :=
λ d, disjoint.comm (disjoint_of_disjoint_cons_left (disjoint.comm d))

lemma disjoint_nil_left (l : list A) : disjoint [] l :=
λ a ab, absurd ab !not_mem_nil

lemma disjoint_nil_right (l : list A) : disjoint l [] :=
disjoint.comm (disjoint_nil_left l)

lemma disjoint_cons_of_not_mem_of_disjoint {a : A} {l₁ l₂} : a ∉ l₂ → disjoint l₁ l₂ → disjoint (a::l₁) l₂ :=
λ nainl₂ d x (xinal₁ : x ∈ a::l₁),
  or.elim (eq_or_mem_of_mem_cons xinal₁)
    (λ xeqa  : x = a, xeqa⁻¹ ▸ nainl₂)
    (λ xinl₁ : x ∈ l₁, disjoint_left d xinl₁)

lemma disjoint_of_disjoint_append_left_left : ∀ {l₁ l₂ l : list A}, disjoint (l₁++l₂) l → disjoint l₁ l
| []      l₂ l d := disjoint_nil_left l
| (x::xs) l₂ l d :=
  have nxinl : x ∉ l, from disjoint_left d !mem_cons,
  have d₁    : disjoint (xs++l₂) l, from disjoint_of_disjoint_cons_left d,
  have d₂    : disjoint xs l, from disjoint_of_disjoint_append_left_left d₁,
  disjoint_cons_of_not_mem_of_disjoint nxinl d₂

lemma disjoint_of_disjoint_append_left_right : ∀ {l₁ l₂ l : list A}, disjoint (l₁++l₂) l → disjoint l₂ l
| []      l₂ l d := d
| (x::xs) l₂ l d :=
  have d₁  : disjoint (xs++l₂) l, from disjoint_of_disjoint_cons_left d,
  disjoint_of_disjoint_append_left_right d₁

lemma disjoint_of_disjoint_append_right_left : ∀ {l₁ l₂ l : list A}, disjoint l (l₁++l₂) → disjoint l l₁ :=
λ l₁ l₂ l d, disjoint.comm (disjoint_of_disjoint_append_left_left (disjoint.comm d))

lemma disjoint_of_disjoint_append_right_right : ∀ {l₁ l₂ l : list A}, disjoint l (l₁++l₂) → disjoint l l₂ :=
λ l₁ l₂ l d, disjoint.comm (disjoint_of_disjoint_append_left_right (disjoint.comm d))

end disjoint

/- no duplicates predicate -/

inductive nodup {A : Type} : list A → Prop :=
| ndnil  : nodup []
| ndcons : ∀ {a l}, a ∉ l → nodup l → nodup (a::l)

section nodup
open nodup
variables {A B : Type}

theorem nodup_nil : @nodup A [] :=
ndnil

theorem nodup_cons {a : A} {l : list A} : a ∉ l → nodup l → nodup (a::l)  :=
λ i n, ndcons i n

theorem nodup_singleton (a : A) : nodup [a] :=
nodup_cons !not_mem_nil nodup_nil

theorem nodup_of_nodup_cons : ∀ {a : A} {l : list A}, nodup (a::l) → nodup l
| a xs (ndcons i n) := n

theorem not_mem_of_nodup_cons : ∀ {a : A} {l : list A}, nodup (a::l) → a ∉ l
| a xs (ndcons i n) := i

theorem not_nodup_cons_of_mem {a : A} {l : list A} : a ∈ l → ¬ nodup (a :: l) :=
λ ainl d, absurd ainl (not_mem_of_nodup_cons d)

theorem not_nodup_cons_of_not_nodup {a : A} {l : list A} : ¬ nodup l → ¬ nodup (a :: l) :=
λ nd d, absurd (nodup_of_nodup_cons d) nd

theorem nodup_of_nodup_append_left : ∀ {l₁ l₂ : list A}, nodup (l₁++l₂) → nodup l₁
| []      l₂ n := nodup_nil
| (x::xs) l₂ n :=
  have ndxs     : nodup xs,   from nodup_of_nodup_append_left (nodup_of_nodup_cons n),
  have nxinxsl₂ : x ∉ xs++l₂, from not_mem_of_nodup_cons n,
  have nxinxs   : x ∉ xs,     from not_mem_of_not_mem_append_left nxinxsl₂,
  nodup_cons nxinxs ndxs

theorem nodup_of_nodup_append_right : ∀ {l₁ l₂ : list A}, nodup (l₁++l₂) → nodup l₂
| []      l₂ n := n
| (x::xs) l₂ n := nodup_of_nodup_append_right (nodup_of_nodup_cons n)

theorem disjoint_of_nodup_append : ∀ {l₁ l₂ : list A}, nodup (l₁++l₂) → disjoint l₁ l₂
| []      l₂  d := disjoint_nil_left l₂
| (x::xs) l₂  d :=
  have nodup (x::(xs++l₂)),    from d,
  have x ∉ xs++l₂,             from not_mem_of_nodup_cons this,
  have nxinl₂ : x ∉ l₂,        from not_mem_of_not_mem_append_right this,
  take a, suppose a ∈ x::xs,
    or.elim (eq_or_mem_of_mem_cons this)
      (suppose a = x, this⁻¹ ▸ nxinl₂)
      (suppose ainxs : a ∈ xs,
        have nodup (x::(xs++l₂)), from d,
        have nodup (xs++l₂),      from nodup_of_nodup_cons this,
        have disjoint xs l₂,      from disjoint_of_nodup_append this,
        disjoint_left this ainxs)

theorem nodup_append_of_nodup_of_nodup_of_disjoint : ∀ {l₁ l₂ : list A}, nodup l₁ → nodup l₂ → disjoint l₁ l₂ → nodup (l₁++l₂)
| []      l₂ d₁ d₂ dsj := by rewrite [append_nil_left]; exact d₂
| (x::xs) l₂ d₁ d₂ dsj :=
  have ndxs     : nodup xs,            from nodup_of_nodup_cons d₁,
  have disjoint xs l₂,                 from disjoint_of_disjoint_cons_left dsj,
  have ndxsl₂   : nodup (xs++l₂),      from nodup_append_of_nodup_of_nodup_of_disjoint ndxs d₂ this,
  have nxinxs   : x ∉ xs,              from not_mem_of_nodup_cons d₁,
  have x ∉ l₂,                         from disjoint_left dsj !mem_cons,
  have x ∉ xs++l₂,                     from not_mem_append nxinxs this,
  nodup_cons this ndxsl₂

theorem nodup_app_comm {l₁ l₂ : list A} (d : nodup (l₁++l₂)) : nodup (l₂++l₁) :=
have d₁  : nodup l₁,       from nodup_of_nodup_append_left d,
have d₂  : nodup l₂,       from nodup_of_nodup_append_right d,
have dsj : disjoint l₁ l₂, from disjoint_of_nodup_append d,
nodup_append_of_nodup_of_nodup_of_disjoint d₂ d₁ (disjoint.comm dsj)

theorem nodup_head {a : A} {l₁ l₂ : list A} (d : nodup (l₁++(a::l₂))) : nodup (a::(l₁++l₂)) :=
have d₁    : nodup (a::(l₂++l₁)), from nodup_app_comm d,
have d₂    : nodup (l₂++l₁),      from nodup_of_nodup_cons d₁,
have d₃    : nodup (l₁++l₂),      from nodup_app_comm d₂,
have nain  : a ∉ l₂++l₁,          from not_mem_of_nodup_cons d₁,
have nain₂ : a ∉ l₂,              from not_mem_of_not_mem_append_left nain,
have nain₁ : a ∉ l₁,              from not_mem_of_not_mem_append_right nain,
nodup_cons (not_mem_append nain₁ nain₂) d₃

theorem nodup_middle {a : A} {l₁ l₂ : list A} (d : nodup (a::(l₁++l₂))) : nodup (l₁++(a::l₂)) :=
have d₁    : nodup (l₁++l₂),      from nodup_of_nodup_cons d,
have nain  : a ∉ l₁++l₂,          from not_mem_of_nodup_cons d,
have disj  : disjoint l₁ l₂,      from disjoint_of_nodup_append d₁,
have d₂    : nodup l₁,            from nodup_of_nodup_append_left d₁,
have d₃    : nodup l₂,            from nodup_of_nodup_append_right d₁,
have nain₂ : a ∉ l₂,              from not_mem_of_not_mem_append_right nain,
have nain₁ : a ∉ l₁,              from not_mem_of_not_mem_append_left nain,
have d₄    : nodup (a::l₂),       from nodup_cons nain₂ d₃,
have disj₂ : disjoint l₁ (a::l₂), from disjoint.comm (disjoint_cons_of_not_mem_of_disjoint nain₁ (disjoint.comm disj)),
nodup_append_of_nodup_of_nodup_of_disjoint d₂ d₄ disj₂

theorem nodup_map {f : A → B} (inj : injective f) : ∀ {l : list A}, nodup l → nodup (map f l)
| []      n := begin rewrite [map_nil], apply nodup_nil end
| (x::xs) n :=
  assert nxinxs : x ∉ xs,           from not_mem_of_nodup_cons n,
  assert ndxs   : nodup xs,         from nodup_of_nodup_cons n,
  assert ndmfxs : nodup (map f xs), from nodup_map ndxs,
  assert nfxinm : f x ∉ map f xs,   from
    λ ab : f x ∈ map f xs,
      obtain (y : A) (yinxs : y ∈ xs) (fyfx : f y = f x), from exists_of_mem_map ab,
      assert yeqx : y = x, from inj fyfx,
      by subst y; contradiction,
  nodup_cons nfxinm ndmfxs

theorem nodup_erase_of_nodup [h : decidable_eq A] (a : A) : ∀ {l}, nodup l → nodup (erase a l)
| []     n := nodup_nil
| (b::l) n := by_cases
  (λ aeqb : a = b, by rewrite [aeqb, erase_cons_head]; exact (nodup_of_nodup_cons n))
  (λ aneb : a ≠ b,
    have nbinl   : b ∉ l,                  from not_mem_of_nodup_cons n,
    have ndl     : nodup l,                from nodup_of_nodup_cons n,
    have ndeal   : nodup (erase a l),      from nodup_erase_of_nodup ndl,
    have nbineal : b ∉ erase a l,          from λ i, absurd (erase_sub _ _ i) nbinl,
    assert aux   : nodup (b :: erase a l), from nodup_cons nbineal ndeal,
    by rewrite [erase_cons_tail _ aneb]; exact aux)

theorem mem_erase_of_nodup [h : decidable_eq A] (a : A) : ∀ {l}, nodup l → a ∉ erase a l
| []     n := !not_mem_nil
| (b::l) n :=
  have ndl     : nodup l,       from nodup_of_nodup_cons n,
  have naineal : a ∉ erase a l, from mem_erase_of_nodup ndl,
  assert nbinl : b ∉ l,         from not_mem_of_nodup_cons n,
  by_cases
  (λ aeqb : a = b, by rewrite [aeqb, erase_cons_head]; exact nbinl)
  (λ aneb : a ≠ b,
    assert aux : a ∉ b :: erase a l, from
      assume ainbeal : a ∈ b :: erase a l, or.elim (eq_or_mem_of_mem_cons ainbeal)
        (λ aeqb   : a = b, absurd aeqb aneb)
        (λ aineal : a ∈ erase a l, absurd aineal naineal),
    by rewrite [erase_cons_tail _ aneb]; exact aux)

definition erase_dup [H : decidable_eq A] : list A → list A
| []        :=  []
| (x :: xs) :=  if x ∈ xs then erase_dup xs else x :: erase_dup xs

theorem erase_dup_nil [H : decidable_eq A] : erase_dup [] = ([] : list A)

theorem erase_dup_cons_of_mem [H : decidable_eq A] {a : A} {l : list A} : a ∈ l → erase_dup (a::l) = erase_dup l :=
assume ainl, calc
  erase_dup (a::l) = if a ∈ l then erase_dup l else a :: erase_dup l : rfl
              ...  = erase_dup l                                     : if_pos ainl

theorem erase_dup_cons_of_not_mem [H : decidable_eq A] {a : A} {l : list A} : a ∉ l → erase_dup (a::l) = a :: erase_dup l :=
assume nainl, calc
  erase_dup (a::l) = if a ∈ l then erase_dup l else a :: erase_dup l : rfl
              ...  = a :: erase_dup l                                : if_neg nainl

theorem mem_erase_dup [H : decidable_eq A] {a : A} : ∀ {l}, a ∈ l → a ∈ erase_dup l
| []     h  := absurd h !not_mem_nil
| (b::l) h  := by_cases
  (λ binl  : b ∈ l, or.elim (eq_or_mem_of_mem_cons h)
    (λ aeqb : a = b, by rewrite [erase_dup_cons_of_mem binl, -aeqb at binl]; exact (mem_erase_dup binl))
    (λ ainl : a ∈ l, by rewrite [erase_dup_cons_of_mem binl]; exact (mem_erase_dup ainl)))
  (λ nbinl : b ∉ l, or.elim (eq_or_mem_of_mem_cons h)
    (λ aeqb : a = b, by rewrite [erase_dup_cons_of_not_mem nbinl, aeqb]; exact !mem_cons)
    (λ ainl : a ∈ l, by rewrite [erase_dup_cons_of_not_mem nbinl]; exact (or.inr (mem_erase_dup ainl))))

theorem mem_of_mem_erase_dup [H : decidable_eq A] {a : A} : ∀ {l}, a ∈ erase_dup l → a ∈ l
| []     h := by rewrite [erase_dup_nil at h]; exact h
| (b::l) h := by_cases
  (λ binl  : b ∈ l,
    have h₁ : a ∈ erase_dup l, by rewrite [erase_dup_cons_of_mem binl at h]; exact h,
    or.inr (mem_of_mem_erase_dup h₁))
  (λ nbinl : b ∉ l,
    have h₁ : a ∈ b :: erase_dup l, by rewrite [erase_dup_cons_of_not_mem nbinl at h]; exact h,
    or.elim (eq_or_mem_of_mem_cons h₁)
      (λ aeqb  : a = b, by rewrite aeqb; exact !mem_cons)
      (λ ainel : a ∈ erase_dup l, or.inr (mem_of_mem_erase_dup ainel)))

theorem erase_dup_sub [H : decidable_eq A] (l : list A) : erase_dup l ⊆ l :=
λ a i, mem_of_mem_erase_dup i

theorem sub_erase_dup [H : decidable_eq A] (l : list A) : l ⊆ erase_dup l :=
λ a i, mem_erase_dup i

theorem nodup_erase_dup [H : decidable_eq A] : ∀ l : list A, nodup (erase_dup l)
| []        := by rewrite erase_dup_nil; exact nodup_nil
| (a::l)    := by_cases
  (λ ainl  : a ∈ l, by rewrite [erase_dup_cons_of_mem ainl]; exact (nodup_erase_dup l))
  (λ nainl : a ∉ l,
    assert r   : nodup (erase_dup l), from nodup_erase_dup l,
    assert nin : a ∉ erase_dup l, from
      assume ab : a ∈ erase_dup l, absurd (mem_of_mem_erase_dup ab) nainl,
    by rewrite [erase_dup_cons_of_not_mem nainl]; exact (nodup_cons nin r))

theorem erase_dup_eq_of_nodup [H : decidable_eq A] : ∀ {l : list A}, nodup l → erase_dup l = l
| []     d := rfl
| (a::l) d :=
  assert nainl : a ∉ l, from not_mem_of_nodup_cons d,
  assert dl : nodup l,  from nodup_of_nodup_cons d,
  by rewrite [erase_dup_cons_of_not_mem nainl, erase_dup_eq_of_nodup dl]

definition decidable_nodup [instance] [h : decidable_eq A] : ∀ (l : list A), decidable (nodup l)
| []     := inl nodup_nil
| (a::l) :=
  match decidable_mem a l with
  | inl p := inr (not_nodup_cons_of_mem p)
  | inr n :=
    match decidable_nodup l with
    | inl nd := inl (nodup_cons n nd)
    | inr d  := inr (not_nodup_cons_of_not_nodup d)
    end
  end

theorem nodup_product : ∀ {l₁ : list A} {l₂ : list B}, nodup l₁ → nodup l₂ → nodup (product l₁ l₂)
| []      l₂ n₁ n₂ := nodup_nil
| (a::l₁) l₂ n₁ n₂ :=
  have nainl₁ : a ∉ l₁,                      from not_mem_of_nodup_cons n₁,
  have n₃    : nodup l₁,                     from nodup_of_nodup_cons n₁,
  have n₄    : nodup (product l₁ l₂),  from nodup_product n₃ n₂,
  have dgen  : ∀ l, nodup l → nodup (map (λ b, (a, b)) l)
    | []     h := nodup_nil
    | (x::l) h :=
      have dl   : nodup l,                      from nodup_of_nodup_cons h,
      have dm   : nodup (map (λ b, (a, b)) l),  from dgen l dl,
      have nxin : x ∉ l,                        from not_mem_of_nodup_cons h,
      have npin : (a, x) ∉ map (λ b, (a, b)) l, from
        assume pin, absurd (mem_of_mem_map_pair₁ pin) nxin,
      nodup_cons npin dm,
  have dm    : nodup (map (λ b, (a, b)) l₂), from dgen l₂ n₂,
  have dsj   : disjoint (map (λ b, (a, b)) l₂) (product l₁ l₂), from
    λ p, match p with
         | (a₁, b₁) :=
            λ (i₁ : (a₁, b₁) ∈ map (λ b, (a, b)) l₂) (i₂ : (a₁, b₁) ∈ product l₁ l₂),
              have a₁inl₁ : a₁ ∈ l₁, from mem_of_mem_product_left i₂,
              have a₁eqa : a₁ = a, from eq_of_mem_map_pair₁ i₁,
              absurd (a₁eqa ▸ a₁inl₁) nainl₁
         end,
  nodup_append_of_nodup_of_nodup_of_disjoint dm n₄ dsj

theorem nodup_filter (p : A → Prop) [h : decidable_pred p] : ∀ {l : list A}, nodup l → nodup (filter p l)
| []     nd := nodup_nil
| (a::l) nd :=
  have   nainl : a ∉ l,              from not_mem_of_nodup_cons nd,
  have   ndl   : nodup l,            from nodup_of_nodup_cons nd,
  assert ndf   : nodup (filter p l), from nodup_filter ndl,
  assert nainf : a ∉ filter p l,     from
    assume ainf, absurd (mem_of_mem_filter ainf) nainl,
  by_cases
    (λ pa  : p a, by rewrite [filter_cons_of_pos _ pa]; exact (nodup_cons nainf ndf))
    (λ npa : ¬ p a, by rewrite [filter_cons_of_neg _ npa]; exact ndf)

lemma dmap_nodup_of_dinj {p : A → Prop} [h : decidable_pred p] {f : Π a, p a → B} (Pdi : dinj p f):
    ∀ {l : list A}, nodup l → nodup (dmap p f l)
| []     := take P, nodup.ndnil
| (a::l) := take Pnodup,
              decidable.rec_on (h a)
                (λ Pa,
                  begin
                    rewrite [dmap_cons_of_pos Pa],
                    apply nodup_cons,
                    apply (not_mem_dmap_of_dinj_of_not_mem Pdi Pa),
                    exact not_mem_of_nodup_cons Pnodup,
                    exact dmap_nodup_of_dinj (nodup_of_nodup_cons Pnodup)
                  end)
                (λ nPa,
                  begin
                    rewrite [dmap_cons_of_neg nPa],
                    exact dmap_nodup_of_dinj (nodup_of_nodup_cons Pnodup)
                  end)

end nodup

/- upto -/
definition upto : nat → list nat
| 0     := []
| (n+1) := n :: upto n

theorem upto_nil  : upto 0 = nil

theorem upto_succ (n : nat) : upto (succ n) = n :: upto n

theorem length_upto : ∀ n, length (upto n) = n
| 0        := rfl
| (succ n) := by rewrite [upto_succ, length_cons, length_upto]

theorem upto_less : ∀ n, all (upto n) (λ i, i < n)
| 0        := trivial
| (succ n) :=
   have alln : all (upto n) (λ i, i < n), from upto_less n,
   all_cons_of_all (lt.base n) (all_implies alln (λ x h, lt.step h))

theorem nodup_upto : ∀ n, nodup (upto n)
| 0     := nodup_nil
| (n+1) :=
  have d : nodup (upto n), from nodup_upto n,
  have n : n ∉ upto n, from
    assume i : n ∈ upto n, absurd (of_mem_of_all i (upto_less n)) (lt.irrefl n),
  nodup_cons n d

theorem lt_of_mem_upto {n i : nat} : i ∈ upto n → i < n :=
assume i, of_mem_of_all i (upto_less n)

theorem mem_upto_succ_of_mem_upto {n i : nat} : i ∈ upto n → i ∈ upto (succ n) :=
assume i, mem_cons_of_mem _ i

theorem mem_upto_of_lt : ∀ {n i : nat}, i < n → i ∈ upto n
| 0        i h := absurd h !not_lt_zero
| (succ n) i h :=
begin
  cases h with m h',
  { rewrite upto_succ, apply mem_cons},
  { exact mem_upto_succ_of_mem_upto (mem_upto_of_lt h')}
end

lemma upto_step : ∀ {n : nat}, upto (succ n) = (map succ (upto n))++[0]
| 0        := rfl
| (succ n) := begin rewrite [upto_succ n, map_cons, append_cons, -upto_step] end

/- union -/
section union
variable {A : Type}
variable [H : decidable_eq A]
include H

definition union : list A → list A → list A
| []      l₂ := l₂
| (a::l₁) l₂ := if a ∈ l₂ then union l₁ l₂ else a :: union l₁ l₂

theorem nil_union (l : list A) : union [] l = l

theorem union_cons_of_mem {a : A} {l₂} : ∀ (l₁), a ∈ l₂ → union (a::l₁) l₂ = union l₁ l₂ :=
take l₁, assume ainl₂, calc
  union (a::l₁) l₂ = if a ∈ l₂ then union l₁ l₂ else a :: union l₁ l₂ : rfl
                  ...   = union l₁ l₂                                           : if_pos ainl₂

theorem union_cons_of_not_mem {a : A} {l₂} : ∀ (l₁), a ∉ l₂ → union (a::l₁) l₂ = a :: union l₁ l₂ :=
take l₁, assume nainl₂, calc
  union (a::l₁) l₂ = if a ∈ l₂ then union l₁ l₂ else a :: union l₁ l₂ : rfl
                  ...   = a :: union l₁ l₂                                      : if_neg nainl₂

theorem union_nil : ∀ (l : list A), union l [] = l
| []     := !nil_union
| (a::l) := by rewrite [union_cons_of_not_mem _ !not_mem_nil, union_nil]

theorem mem_or_mem_of_mem_union : ∀ {l₁ l₂} {a : A}, a ∈ union l₁ l₂ → a ∈ l₁ ∨ a ∈ l₂
| []      l₂ a ainl₂ := by rewrite nil_union at ainl₂; exact (or.inr (ainl₂))
| (b::l₁) l₂ a ainbl₁l₂ := by_cases
  (λ binl₂  : b ∈ l₂,
    have ainl₁l₂ : a ∈ union l₁ l₂, by rewrite [union_cons_of_mem l₁ binl₂ at ainbl₁l₂]; exact ainbl₁l₂,
    or.elim (mem_or_mem_of_mem_union ainl₁l₂)
      (λ ainl₁, or.inl (mem_cons_of_mem _ ainl₁))
      (λ ainl₂, or.inr ainl₂))
  (λ nbinl₂ : b ∉ l₂,
    have ainb_l₁l₂ : a ∈ b :: union l₁ l₂, by rewrite [union_cons_of_not_mem l₁ nbinl₂ at ainbl₁l₂]; exact ainbl₁l₂,
    or.elim (eq_or_mem_of_mem_cons ainb_l₁l₂)
      (λ aeqb, by rewrite aeqb; exact (or.inl !mem_cons))
      (λ ainl₁l₂,
        or.elim (mem_or_mem_of_mem_union ainl₁l₂)
          (λ ainl₁, or.inl (mem_cons_of_mem _ ainl₁))
          (λ ainl₂, or.inr ainl₂)))

theorem mem_union_right {a : A} : ∀ (l₁) {l₂}, a ∈ l₂ → a ∈ union l₁ l₂
| []      l₂  h := by rewrite nil_union; exact h
| (b::l₁) l₂  h := by_cases
  (λ binl₂ : b ∈ l₂, by rewrite [union_cons_of_mem _ binl₂]; exact (mem_union_right _ h))
  (λ nbinl₂ : b ∉ l₂, by rewrite [union_cons_of_not_mem _ nbinl₂]; exact (mem_cons_of_mem _ (mem_union_right _ h)))

theorem mem_union_left {a : A} : ∀ {l₁} (l₂), a ∈ l₁ → a ∈ union l₁ l₂
| []      l₂  h := absurd h !not_mem_nil
| (b::l₁) l₂  h := by_cases
  (λ binl₂  : b ∈ l₂, or.elim (eq_or_mem_of_mem_cons h)
    (λ aeqb  : a = b,
      by rewrite [union_cons_of_mem l₁ binl₂, -aeqb at binl₂]; exact (mem_union_right _ binl₂))
    (λ ainl₁ : a ∈ l₁,
      by rewrite [union_cons_of_mem l₁ binl₂]; exact (mem_union_left _ ainl₁)))
  (λ nbinl₂ : b ∉ l₂, or.elim (eq_or_mem_of_mem_cons h)
    (λ aeqb  : a = b,
      by rewrite [union_cons_of_not_mem l₁ nbinl₂, aeqb]; exact !mem_cons)
    (λ ainl₁ : a ∈ l₁,
      by rewrite [union_cons_of_not_mem l₁ nbinl₂]; exact (mem_cons_of_mem _ (mem_union_left _ ainl₁))))

theorem mem_union_cons (a : A) (l₁ : list A) (l₂ : list A) : a ∈ union (a::l₁) l₂ :=
by_cases
  (λ ainl₂  : a ∈ l₂, mem_union_right _ ainl₂)
  (λ nainl₂ : a ∉ l₂, by rewrite [union_cons_of_not_mem _ nainl₂]; exact !mem_cons)

theorem nodup_union_of_nodup_of_nodup : ∀ {l₁ l₂ : list A}, nodup l₁ → nodup l₂ → nodup (union l₁ l₂)
| []      l₂ n₁   nl₂ := by rewrite nil_union; exact nl₂
| (a::l₁) l₂ nal₁ nl₂ :=
  assert nl₁   : nodup l₁, from nodup_of_nodup_cons nal₁,
  assert nl₁l₂ : nodup (union l₁ l₂), from nodup_union_of_nodup_of_nodup nl₁ nl₂,
  by_cases
    (λ ainl₂  : a ∈ l₂,
       by rewrite [union_cons_of_mem l₁ ainl₂]; exact nl₁l₂)
    (λ nainl₂ : a ∉ l₂,
       have nainl₁ : a ∉ l₁, from not_mem_of_nodup_cons nal₁,
       assert nainl₁l₂ : a ∉ union l₁ l₂, from
         assume ainl₁l₂ : a ∈ union l₁ l₂, or.elim (mem_or_mem_of_mem_union ainl₁l₂)
           (λ ainl₁, absurd ainl₁ nainl₁)
           (λ ainl₂, absurd ainl₂ nainl₂),
       by rewrite [union_cons_of_not_mem l₁ nainl₂]; exact (nodup_cons nainl₁l₂ nl₁l₂))

theorem union_eq_append : ∀ {l₁ l₂ : list A}, disjoint l₁ l₂ → union l₁ l₂ = append l₁ l₂
| []      l₂ d := rfl
| (a::l₁) l₂ d :=
  assert nainl₂ : a ∉ l₂, from disjoint_left d !mem_cons,
  assert d₁ : disjoint l₁ l₂, from disjoint_of_disjoint_cons_left d,
  by rewrite [union_cons_of_not_mem _ nainl₂, append_cons, union_eq_append d₁]

theorem all_union {p : A → Prop} : ∀ {l₁ l₂ : list A}, all l₁ p → all l₂ p → all (union l₁ l₂) p
| []      l₂ h₁ h₂ := h₂
| (a::l₁) l₂ h₁ h₂ :=
  have h₁'   : all l₁ p, from all_of_all_cons h₁,
  have pa    : p a, from of_all_cons h₁,
  assert au  : all (union l₁ l₂) p, from all_union h₁' h₂,
  assert au' : all (a :: union l₁ l₂) p, from all_cons_of_all pa au,
  by_cases
    (λ ainl₂  : a ∈ l₂, by rewrite [union_cons_of_mem _ ainl₂]; exact au)
    (λ nainl₂ : a ∉ l₂, by rewrite [union_cons_of_not_mem _ nainl₂]; exact au')

theorem all_of_all_union_left {p : A → Prop} : ∀ {l₁ l₂ : list A}, all (union l₁ l₂) p → all l₁ p
| []      l₂  h := trivial
| (a::l₁) l₂  h :=
  have ain : a ∈ union (a::l₁) l₂, from !mem_union_cons,
  have pa  : p a, from of_mem_of_all ain h,
  by_cases
  (λ ainl₂  : a ∈ l₂,
    have al₁l₂ : all (union l₁ l₂) p, by rewrite [union_cons_of_mem _ ainl₂ at h]; exact h,
    have al₁   : all l₁ p, from all_of_all_union_left al₁l₂,
    all_cons_of_all pa al₁)
  (λ nainl₂ : a ∉ l₂,
    have aal₁l₂ : all (a::union l₁ l₂) p, by rewrite [union_cons_of_not_mem _ nainl₂ at h]; exact h,
    have al₁l₂ : all (union l₁ l₂) p, from all_of_all_cons aal₁l₂,
    have al₁   : all l₁ p, from all_of_all_union_left al₁l₂,
    all_cons_of_all pa al₁)

theorem all_of_all_union_right {p : A → Prop} : ∀ {l₁ l₂ : list A}, all (union l₁ l₂) p → all l₂ p
| []      l₂ h := by rewrite [nil_union at h]; exact h
| (a::l₁) l₂ h := by_cases
  (λ ainl₂  : a ∈ l₂, by rewrite [union_cons_of_mem _ ainl₂ at h]; exact (all_of_all_union_right h))
  (λ nainl₂ : a ∉ l₂,
    have h₁ : all (a :: union l₁ l₂) p, by rewrite [union_cons_of_not_mem _ nainl₂ at h]; exact h,
    all_of_all_union_right (all_of_all_cons h₁))

variable {B : Type}
theorem foldl_union_of_disjoint (f : B → A → B) (b : B) {l₁ l₂ : list A} (d : disjoint l₁ l₂)
        : foldl f b (union l₁ l₂) = foldl f (foldl f b l₁) l₂ :=
by rewrite [union_eq_append d, foldl_append]

theorem foldr_union_of_dijoint  (f : A → B → B) (b : B) {l₁ l₂ : list A} (d : disjoint l₁ l₂)
        : foldr f b (union l₁ l₂) = foldr f (foldr f b l₂) l₁ :=
by rewrite [union_eq_append d, foldr_append]
end union

/- insert -/
section insert
variable {A : Type}
variable [H : decidable_eq A]
include H

definition insert (a : A) (l : list A) : list A :=
if a ∈ l then l else a::l

theorem insert_eq_of_mem {a : A} {l : list A} : a ∈ l → insert a l = l :=
assume ainl, if_pos ainl

theorem insert_eq_of_not_mem {a : A} {l : list A} : a ∉ l → insert a l = a::l :=
assume nainl, if_neg nainl

theorem mem_insert (a : A) (l : list A) : a ∈ insert a l :=
by_cases
  (λ ainl  : a ∈ l, by rewrite [insert_eq_of_mem ainl]; exact ainl)
  (λ nainl : a ∉ l, by rewrite [insert_eq_of_not_mem nainl]; exact !mem_cons)

theorem mem_insert_of_mem {a : A} (b : A) {l : list A} : a ∈ l → a ∈ insert b l :=
assume ainl, by_cases
  (λ binl  : b ∈ l, by rewrite [insert_eq_of_mem binl]; exact ainl)
  (λ nbinl : b ∉ l, by rewrite [insert_eq_of_not_mem nbinl]; exact (mem_cons_of_mem _ ainl))

theorem eq_or_mem_of_mem_insert {x a : A} {l : list A} (H : x ∈ insert a l) : x = a ∨ x ∈ l :=
decidable.by_cases
  (assume H3: a ∈ l, or.inr (insert_eq_of_mem H3 ▸ H))
  (assume H3: a ∉ l,
    have H4: x ∈ a :: l, from insert_eq_of_not_mem H3 ▸ H,
    iff.mp !mem_cons_iff H4)

theorem mem_insert_iff (x a : A) (l : list A) : x ∈ insert a l ↔ x = a ∨ x ∈ l :=
iff.intro
  (!eq_or_mem_of_mem_insert)
  (assume H, or.elim H
    (assume H' : x = a, H'⁻¹ ▸ !mem_insert)
    (assume H' : x ∈ l, !mem_insert_of_mem H'))

theorem nodup_insert (a : A) {l : list A} : nodup l → nodup (insert a l) :=
assume n, by_cases
  (λ ainl  : a ∈ l, by rewrite [insert_eq_of_mem ainl]; exact n)
  (λ nainl : a ∉ l, by rewrite [insert_eq_of_not_mem nainl]; exact (nodup_cons nainl n))

theorem length_insert_of_mem {a : A} {l : list A} : a ∈ l → length (insert a l) = length l :=
assume ainl, by rewrite [insert_eq_of_mem ainl]

theorem length_insert_of_not_mem {a : A} {l : list A} : a ∉ l → length (insert a l) = length l + 1 :=
assume nainl, by rewrite [insert_eq_of_not_mem nainl]

theorem all_insert_of_all {p : A → Prop} {a : A} {l} : p a → all l p → all (insert a l) p :=
assume h₁ h₂, by_cases
  (λ ainl  : a ∈ l, by rewrite [insert_eq_of_mem ainl]; exact h₂)
  (λ nainl : a ∉ l, by rewrite [insert_eq_of_not_mem nainl]; exact (all_cons_of_all h₁ h₂))
end insert

/- inter -/
section inter
variable {A : Type}
variable [H : decidable_eq A]
include H

definition inter : list A → list A → list A
| []      l₂ := []
| (a::l₁) l₂ := if a ∈ l₂ then a :: inter l₁ l₂ else inter l₁ l₂

theorem inter_nil (l : list A) : inter [] l = []

theorem inter_cons_of_mem {a : A} (l₁ : list A) {l₂} : a ∈ l₂ → inter (a::l₁) l₂ = a :: inter l₁ l₂ :=
assume i, if_pos i

theorem inter_cons_of_not_mem {a : A} (l₁ : list A) {l₂} : a ∉ l₂ → inter (a::l₁) l₂ = inter l₁ l₂ :=
assume i, if_neg i

theorem mem_of_mem_inter_left : ∀ {l₁ l₂} {a : A}, a ∈ inter l₁ l₂ → a ∈ l₁
| []      l₂ a i := absurd i !not_mem_nil
| (b::l₁) l₂ a i := by_cases
  (λ binl₂  : b ∈ l₂,
    have aux : a ∈ b :: inter l₁ l₂, by rewrite [inter_cons_of_mem _ binl₂ at i]; exact i,
    or.elim (eq_or_mem_of_mem_cons aux)
      (λ aeqb : a = b, by rewrite [aeqb]; exact !mem_cons)
      (λ aini, mem_cons_of_mem _ (mem_of_mem_inter_left aini)))
  (λ nbinl₂ : b ∉ l₂,
    have ainl₁ : a ∈ l₁, by rewrite [inter_cons_of_not_mem _ nbinl₂ at i]; exact (mem_of_mem_inter_left i),
    mem_cons_of_mem _ ainl₁)

theorem mem_of_mem_inter_right : ∀ {l₁ l₂} {a : A}, a ∈ inter l₁ l₂ → a ∈ l₂
| []      l₂ a i := absurd i !not_mem_nil
| (b::l₁) l₂ a i := by_cases
  (λ binl₂  : b ∈ l₂,
    have aux : a ∈ b :: inter l₁ l₂, by rewrite [inter_cons_of_mem _ binl₂ at i]; exact i,
    or.elim (eq_or_mem_of_mem_cons aux)
      (λ aeqb : a = b, by rewrite [aeqb]; exact binl₂)
      (λ aini : a ∈ inter l₁ l₂, mem_of_mem_inter_right aini))
  (λ nbinl₂ : b ∉ l₂,
    by rewrite [inter_cons_of_not_mem _ nbinl₂ at i]; exact (mem_of_mem_inter_right i))

theorem mem_inter_of_mem_of_mem : ∀ {l₁ l₂} {a : A}, a ∈ l₁ → a ∈ l₂ → a ∈ inter l₁ l₂
| []      l₂ a i₁ i₂ := absurd i₁ !not_mem_nil
| (b::l₁) l₂ a i₁ i₂ := by_cases
  (λ binl₂  : b ∈ l₂,
    or.elim (eq_or_mem_of_mem_cons i₁)
      (λ aeqb  : a = b,
        by rewrite [inter_cons_of_mem _ binl₂, aeqb]; exact !mem_cons)
     (λ ainl₁ : a ∈ l₁,
        by rewrite [inter_cons_of_mem _ binl₂];
           apply mem_cons_of_mem;
           exact (mem_inter_of_mem_of_mem ainl₁ i₂)))
  (λ nbinl₂ : b ∉ l₂,
    or.elim (eq_or_mem_of_mem_cons i₁)
     (λ aeqb  : a = b, absurd (aeqb ▸ i₂) nbinl₂)
     (λ ainl₁ : a ∈ l₁,
       by rewrite [inter_cons_of_not_mem _ nbinl₂]; exact (mem_inter_of_mem_of_mem ainl₁ i₂)))

theorem nodup_inter_of_nodup : ∀ {l₁ : list A} (l₂), nodup l₁ → nodup (inter l₁ l₂)
| []      l₂ d := nodup_nil
| (a::l₁) l₂ d :=
  have   d₁     : nodup l₁,            from nodup_of_nodup_cons d,
  assert d₂     : nodup (inter l₁ l₂), from nodup_inter_of_nodup _ d₁,
  have   nainl₁ : a ∉ l₁,              from not_mem_of_nodup_cons d,
  assert naini  : a ∉ inter l₁ l₂,     from λ i, absurd (mem_of_mem_inter_left i) nainl₁,
  by_cases
    (λ ainl₂  : a ∈ l₂, by rewrite [inter_cons_of_mem _ ainl₂]; exact (nodup_cons naini d₂))
    (λ nainl₂ : a ∉ l₂, by rewrite [inter_cons_of_not_mem _ nainl₂]; exact d₂)

theorem inter_eq_nil_of_disjoint : ∀ {l₁ l₂ : list A}, disjoint l₁ l₂ → inter l₁ l₂ = []
| []      l₂ d := rfl
| (a::l₁) l₂ d :=
  assert aux_eq : inter l₁ l₂ = [], from inter_eq_nil_of_disjoint (disjoint_of_disjoint_cons_left d),
  assert nainl₂ : a ∉ l₂,           from disjoint_left d !mem_cons,
  by rewrite [inter_cons_of_not_mem _ nainl₂, aux_eq]

theorem all_inter_of_all_left {p : A → Prop} : ∀ {l₁} (l₂), all l₁ p → all (inter l₁ l₂) p
| []      l₂ h := trivial
| (a::l₁) l₂ h :=
  have   h₁ : all l₁ p,                 from all_of_all_cons h,
  assert h₂ : all (inter l₁ l₂) p,      from all_inter_of_all_left _ h₁,
  have   pa : p a,                      from of_all_cons h,
  assert h₃ : all (a :: inter l₁ l₂) p, from all_cons_of_all pa h₂,
  by_cases
    (λ ainl₂  : a ∈ l₂, by rewrite [inter_cons_of_mem _ ainl₂]; exact h₃)
    (λ nainl₂ : a ∉ l₂, by rewrite [inter_cons_of_not_mem _ nainl₂]; exact h₂)

theorem all_inter_of_all_right {p : A → Prop} : ∀ (l₁) {l₂}, all l₂ p → all (inter l₁ l₂) p
| []      l₂ h := trivial
| (a::l₁) l₂ h :=
  assert h₁ : all (inter l₁ l₂) p, from all_inter_of_all_right _ h,
  by_cases
    (λ ainl₂  : a ∈ l₂,
      have   pa : p a,                      from of_mem_of_all ainl₂ h,
      assert h₂ : all (a :: inter l₁ l₂) p, from all_cons_of_all pa h₁,
      by rewrite [inter_cons_of_mem _ ainl₂]; exact h₂)
    (λ nainl₂ : a ∉ l₂, by rewrite [inter_cons_of_not_mem _ nainl₂]; exact h₁)

end inter
end list
