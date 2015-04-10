/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.list.set
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
   (λ aeqx : a = x, by rewrite [aeqx, erase_cons_head])
   (λ anex : a ≠ x,
    assert ainyxs : a ∈ y::xs, from or_resolve_right h anex,
    by rewrite [erase_cons_tail _ anex, *length_cons, length_erase_of_mem ainyxs])

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
    assert nainxs : a ∉ xs, from not_mem_of_not_mem h,
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
end erase

/- disjoint -/
section disjoint
variable {A : Type}

definition disjoint (l₁ l₂ : list A) : Prop := ∀ a, (a ∈ l₁ → a ∉ l₂) ∧ (a ∈ l₂ → a ∉ l₁)

lemma disjoint_left {l₁ l₂ : list A} : disjoint l₁ l₂ → ∀ {a}, a ∈ l₁ → a ∉ l₂ :=
λ d a, and.elim_left (d a)

lemma disjoint_right {l₁ l₂ : list A} : disjoint l₁ l₂ → ∀ {a}, a ∈ l₂ → a ∉ l₁ :=
λ d a, and.elim_right (d a)

lemma disjoint.comm {l₁ l₂ : list A} : disjoint l₁ l₂ → disjoint l₂ l₁ :=
λ d a, and.intro
  (λ ainl₂ : a ∈ l₂, disjoint_right d ainl₂)
  (λ ainl₁ : a ∈ l₁, disjoint_left d ainl₁)

lemma disjoint_of_disjoint_cons_left {a : A} {l₁ l₂} : disjoint (a::l₁) l₂ → disjoint l₁ l₂ :=
λ d x, and.intro
  (λ xinl₁ : x ∈ l₁, disjoint_left d (or.inr xinl₁))
  (λ xinl₂ : x ∈ l₂,
    have nxinal₁ : x ∉ a::l₁, from disjoint_right d xinl₂,
    not_mem_of_not_mem nxinal₁)

lemma disjoint_of_disjoint_cons_right {a : A} {l₁ l₂} : disjoint l₁ (a::l₂) → disjoint l₁ l₂ :=
λ d, disjoint.comm (disjoint_of_disjoint_cons_left (disjoint.comm d))

lemma disjoint_nil_left (l : list A) : disjoint [] l :=
λ a, and.intro
  (λ ab   : a ∈ nil, absurd ab !not_mem_nil)
  (λ ainl : a ∈ l, !not_mem_nil)

lemma disjoint_nil_right (l : list A) : disjoint l [] :=
disjoint.comm (disjoint_nil_left l)

lemma disjoint_cons_of_not_mem_of_disjoint {a : A} {l₁ l₂} : a ∉ l₂ → disjoint l₁ l₂ → disjoint (a::l₁) l₂ :=
λ nainl₂ d x, and.intro
  (λ xinal₁ : x ∈ a::l₁, or.elim (eq_or_mem_of_mem_cons xinal₁)
    (λ xeqa  : x = a, xeqa⁻¹ ▸ nainl₂)
    (λ xinl₁ : x ∈ l₁, disjoint_left d xinl₁))
  (λ (xinl₂ : x ∈ l₂) (xinal₁ : x ∈ a::l₁), or.elim (eq_or_mem_of_mem_cons xinal₁)
    (λ xeqa  : x = a, absurd (xeqa ▸ xinl₂) nainl₂)
    (λ xinl₁ : x ∈ l₁, absurd xinl₁ (disjoint_right d xinl₂)))

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

theorem nodup_of_nodup_cons : ∀ {a : A} {l : list A}, nodup (a::l) → nodup l
| a xs (ndcons i n) := n

theorem not_mem_of_nodup_cons : ∀ {a : A} {l : list A}, nodup (a::l) → a ∉ l
| a xs (ndcons i n) := i

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
  have d₁     : nodup (x::(xs++l₂)), from d,
  have d₂     : nodup (xs++l₂),      from nodup_of_nodup_cons d₁,
  have nxin   : x ∉ xs++l₂,          from not_mem_of_nodup_cons d₁,
  have nxinl₂ : x ∉ l₂,              from not_mem_of_not_mem_append_right nxin,
  have dsj    : disjoint xs l₂,      from disjoint_of_nodup_append d₂,
  (λ a, and.intro
    (λ ainxxs : a ∈ x::xs,
      or.elim (eq_or_mem_of_mem_cons ainxxs)
        (λ aeqx  : a = x, aeqx⁻¹ ▸ nxinl₂)
        (λ ainxs : a ∈ xs, disjoint_left dsj ainxs))
    (λ ainl₂  : a ∈ l₂,
      have nainxs : a ∉ xs, from disjoint_right dsj ainl₂,
      assume ain : a ∈ x::xs, or.elim (eq_or_mem_of_mem_cons ain)
       (λ aeqx  : a = x, absurd (aeqx ▸ ainl₂) nxinl₂)
       (λ ainxs : a ∈ xs, absurd ainxs nainxs)))

theorem nodup_append_of_nodup_of_nodup_of_disjoint : ∀ {l₁ l₂ : list A}, nodup l₁ → nodup l₂ → disjoint l₁ l₂ → nodup (l₁++l₂)
| []      l₂ d₁ d₂ dsj := by rewrite [append_nil_left]; exact d₂
| (x::xs) l₂ d₁ d₂ dsj :=
  have dsj₁     : disjoint xs l₂,      from disjoint_of_disjoint_cons_left dsj,
  have ndxs     : nodup xs,            from nodup_of_nodup_cons d₁,
  have ndxsl₂   : nodup (xs++l₂),      from nodup_append_of_nodup_of_nodup_of_disjoint ndxs d₂ dsj₁,
  have nxinxs   : x ∉ xs,              from not_mem_of_nodup_cons d₁,
  have nxinl₂   : x ∉ l₂,              from disjoint_left dsj !mem_cons,
  have nxinxsl₂ : x ∉ xs++l₂,          from not_mem_append nxinxs nxinl₂,
  nodup_cons nxinxsl₂ ndxsl₂

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
      obtain (finv : B → A) (isinv : finv ∘ f = id), from inj,
      assert finvfxin : finv (f x) ∈ map finv (map f xs), from mem_map finv ab,
      assert xinxs : x ∈ xs,
        begin
          rewrite [map_map at finvfxin, isinv at finvfxin, left_inv_eq isinv at finvfxin],
          rewrite [map_id at finvfxin],
          exact finvfxin
        end,
      absurd xinxs nxinxs,
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

theorem erase_dup_nil [H : decidable_eq A] : erase_dup [] = []

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
end nodup

/- union -/
section union
variable {A : Type}
variable [H : decidable_eq A]
include H

definition union : list A → list A → list A
| []      l₂ := l₂
| (a::l₁) l₂ := if a ∈ l₂ then union l₁ l₂ else a :: union l₁ l₂

theorem union_nil (l : list A) : union [] l = l

theorem union_cons_of_mem {a : A} {l₂} : ∀ (l₁), a ∈ l₂ → union (a::l₁) l₂ = union l₁ l₂ :=
take l₁, assume ainl₂, calc
  union (a::l₁) l₂ = if a ∈ l₂ then union l₁ l₂ else a :: union l₁ l₂ : rfl
                  ...   = union l₁ l₂                                           : if_pos ainl₂

theorem union_cons_of_not_mem {a : A} {l₂} : ∀ (l₁), a ∉ l₂ → union (a::l₁) l₂ = a :: union l₁ l₂ :=
take l₁, assume nainl₂, calc
  union (a::l₁) l₂ = if a ∈ l₂ then union l₁ l₂ else a :: union l₁ l₂ : rfl
                  ...   = a :: union l₁ l₂                                      : if_neg nainl₂

theorem mem_or_mem_of_mem_union : ∀ {l₁ l₂} {a : A}, a ∈ union l₁ l₂ → a ∈ l₁ ∨ a ∈ l₂
| []      l₂ a ainl₂ := by rewrite union_nil at ainl₂; exact (or.inr (ainl₂))
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
| []      l₂  h := by rewrite union_nil; exact h
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

theorem nodup_union_of_nodup_of_nodup : ∀ {l₁ l₂ : list A}, nodup l₁ → nodup l₂ → nodup (union l₁ l₂)
| []      l₂ n₁   nl₂ := by rewrite union_nil; exact nl₂
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

theorem nodup_insert (a : A) {l : list A} : nodup l → nodup (insert a l) :=
assume n, by_cases
  (λ ainl  : a ∈ l, by rewrite [insert_eq_of_mem ainl]; exact n)
  (λ nainl : a ∉ l, by rewrite [insert_eq_of_not_mem nainl]; exact (nodup_cons nainl n))

theorem length_insert_of_mem {a : A} {l : list A} : a ∈ l → length (insert a l) = length l :=
assume ainl, by rewrite [insert_eq_of_mem ainl]

theorem length_insert_of_not_mem {a : A} {l : list A} : a ∉ l → length (insert a l) = length l + 1 :=
assume nainl, by rewrite [insert_eq_of_not_mem nainl]
end insert
end list
