/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import data.nat data.list data.equiv
open nat function option

definition stream (A : Type) := nat → A

namespace stream
variables {A B C : Type}

definition cons (a : A) (s : stream A) : stream A :=
λ i,
  match i with
  | 0      := a
  | succ n := s n
  end

notation h :: t := cons h t

definition head [reducible] (s : stream A) : A :=
s 0

definition tail (s : stream A) : stream A :=
λ i, s (i+1)

definition drop (n : nat) (s : stream A) : stream A :=
λ i, s (i+n)

definition nth [reducible] (n : nat) (s : stream A) : A :=
s n

protected theorem eta (s : stream A) : head s :: tail s = s :=
funext (λ i, begin cases i, repeat reflexivity end)

theorem nth_zero_cons (a : A) (s : stream A) : nth 0 (a :: s) = a :=
rfl

theorem head_cons (a : A) (s : stream A) : head (a :: s) = a :=
rfl

theorem tail_cons (a : A) (s : stream A) : tail (a :: s) = s :=
rfl

theorem tail_drop (n : nat) (s : stream A) : tail (drop n s) = drop n (tail s) :=
funext (λ i, begin esimp [tail, drop], congruence, rewrite add.right_comm end)

theorem nth_drop (n m : nat) (s : stream A) : nth n (drop m s) = nth (n+m) s :=
rfl

theorem tail_eq_drop (s : stream A) : tail s = drop 1 s :=
rfl

theorem drop_drop (n m : nat) (s : stream A) : drop n (drop m s) = drop (n+m) s :=
funext (λ i, begin esimp [drop], rewrite add.assoc end)

theorem nth_succ (n : nat) (s : stream A) : nth (succ n) s = nth n (tail s) :=
rfl

theorem drop_succ (n : nat) (s : stream A) : drop (succ n) s = drop n (tail s) :=
rfl

protected theorem ext {s₁ s₂ : stream A} : (∀ n, nth n s₁ = nth n s₂) → s₁ = s₂ :=
assume h, funext h

definition all (p : A → Prop) (s : stream A) := ∀ n, p (nth n s)

definition any (p : A → Prop) (s : stream A) := ∃ n, p (nth n s)

theorem all_def (p : A → Prop) (s : stream A) : all p s = ∀ n, p (nth n s) :=
rfl

theorem any_def (p : A → Prop) (s : stream A) : any p s = ∃ n, p (nth n s) :=
rfl

definition mem (a : A) (s : stream A) := any (λ b, a = b) s

notation e ∈ s := mem e s

theorem mem_cons (a : A) (s : stream A) : a ∈ (a::s) :=
exists.intro 0 rfl

theorem mem_cons_of_mem {a : A} {s : stream A} (b : A) : a ∈ s → a ∈ b :: s :=
assume ains, obtain n (h : a = nth n s), from ains,
exists.intro (succ n) (by rewrite [nth_succ, tail_cons, h])

theorem eq_or_mem_of_mem_cons {a b : A} {s : stream A} : a ∈ b::s → a = b ∨ a ∈ s :=
assume ainbs, obtain n (h : a = nth n (b::s)), from ainbs,
begin
  cases n with n',
   {left, exact h},
   {right, rewrite [nth_succ at h, tail_cons at h], existsi n', exact h}
end

theorem mem_of_nth_eq {n : nat} {s : stream A} {a : A} : a = nth n s → a ∈ s :=
assume h, exists.intro n h

section map
variable (f : A → B)

definition map (s : stream A) : stream B :=
λ n, f (nth n s)

theorem drop_map (n : nat) (s : stream A) : drop n (map f s) = map f (drop n s) :=
stream.ext (λ i, rfl)

theorem nth_map (n : nat) (s : stream A) : nth n (map f s) = f (nth n s) :=
rfl

theorem tail_map (s : stream A) : tail (map f s) = map f (tail s) :=
begin rewrite tail_eq_drop end

theorem head_map (s : stream A) : head (map f s) = f (head s) :=
rfl

theorem map_eq (s : stream A) : map f s = f (head s) :: map f (tail s) :=
by rewrite [-stream.eta, tail_map, head_map]

theorem map_cons (a : A) (s : stream A) : map f (a :: s) = f a :: map f s :=
by rewrite [-stream.eta, map_eq]

theorem map_id (s : stream A) : map id s = s :=
rfl

theorem map_map (g : B → C) (f : A → B) (s : stream A) : map g (map f s) = map (g ∘ f) s :=
rfl

theorem mem_map {a : A} {s : stream A} : a ∈ s → f a ∈ map f s :=
assume ains, obtain n (h : a = nth n s), from ains,
exists.intro n (by rewrite [nth_map, h])
end map

section zip
variable (f : A → B → C)

definition zip (s₁ : stream A) (s₂ : stream B) : stream C :=
λ n, f (nth n s₁) (nth n s₂)

theorem drop_zip (n : nat) (s₁ : stream A) (s₂ : stream B) : drop n (zip f s₁ s₂) = zip f (drop n s₁) (drop n s₂) :=
stream.ext (λ i, rfl)

theorem nth_zip (n : nat) (s₁ : stream A) (s₂ : stream B) : nth n (zip f s₁ s₂) = f (nth n s₁) (nth n s₂) :=
rfl

theorem head_zip (s₁ : stream A) (s₂ : stream B) : head (zip f s₁ s₂) = f (head s₁) (head s₂) :=
rfl

theorem tail_zip (s₁ : stream A) (s₂ : stream B) : tail (zip f s₁ s₂) = zip f (tail s₁) (tail s₂) :=
rfl

theorem zip_eq (s₁ : stream A) (s₂ : stream B) : zip f s₁ s₂ = f (head s₁) (head s₂) :: zip f (tail s₁) (tail s₂) :=
by rewrite [-stream.eta]
end zip

definition const (a : A) : stream A :=
λ n, a

theorem mem_const (a : A) : a ∈ const a :=
exists.intro 0 rfl

theorem const_eq (a : A) : const a = a :: const a :=
begin
  apply stream.ext, intro n,
  cases n, repeat reflexivity
end

theorem tail_const (a : A) : tail (const a) = const a :=
by rewrite [const_eq at {1}]

theorem map_const (f : A → B) (a : A) : map f (const a) = const (f a) :=
rfl

theorem nth_const (n : nat) (a : A) : nth n (const a) = a :=
rfl

theorem drop_const (n : nat) (a : A) : drop n (const a) = const a :=
stream.ext (λ i, rfl)

definition iterate (f : A → A) (a : A) : stream A :=
λ n, nat.rec_on n a (λ n r, f r)

theorem head_iterate (f : A → A) (a : A) : head (iterate f a) = a :=
rfl

theorem tail_iterate (f : A → A) (a : A) : tail (iterate f a) = iterate f (f a) :=
begin
  apply funext, intro n,
  induction n with n' IH,
    {reflexivity},
    {esimp [tail, iterate] at *,
     rewrite add_one at *,
     esimp at *, rewrite IH}
end

theorem iterate_eq (f : A → A) (a : A) : iterate f a = a :: iterate f (f a) :=
begin
  rewrite [-stream.eta], congruence, exact !tail_iterate
end

theorem nth_zero_iterate (f : A → A) (a : A) : nth 0 (iterate f a) = a :=
rfl

theorem nth_succ_iterate (n : nat) (f : A → A) (a : A) : nth (succ n) (iterate f a) = nth n (iterate f (f a)) :=
by rewrite [nth_succ, tail_iterate]

section bisim
  variable (R : stream A → stream A → Prop)
  local infix ~ := R

  definition is_bisimulation := ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ → head s₁ = head s₂ ∧ tail s₁ ~ tail s₂

  lemma nth_of_bisim (bisim : is_bisimulation R) : ∀ {s₁ s₂} n, s₁ ~ s₂ → nth n s₁ = nth n s₂ ∧ drop (n+1) s₁ ~ drop (n+1) s₂
  | s₁ s₂ 0     h := bisim h
  | s₁ s₂ (n+1) h :=
    obtain h₁ (trel : tail s₁ ~ tail s₂), from bisim h,
    nth_of_bisim n trel

  -- If two streams are bisimilar, then they are equal
  theorem eq_of_bisim (bisim : is_bisimulation R) : ∀ {s₁ s₂}, s₁ ~ s₂ → s₁ = s₂ :=
  λ s₁ s₂ r, stream.ext (λ n, and.elim_left (nth_of_bisim R bisim n r))
end bisim

theorem bisim_simple (s₁ s₂ : stream A) : head s₁ = head s₂ → s₁ = tail s₁ → s₂ = tail s₂ → s₁ = s₂ :=
assume hh ht₁ ht₂, eq_of_bisim
  (λ s₁ s₂, head s₁ = head s₂ ∧ s₁ = tail s₁ ∧ s₂ = tail s₂)
  (λ s₁ s₂ h,
    obtain h₁ h₂ h₃, from h,
    begin
      constructor, exact h₁, rewrite [-h₂, -h₃], exact h
    end)
  (and.intro hh (and.intro ht₁ ht₂))

-- AKA coinduction freeze
theorem coinduction.{l} {A : Type.{l}} {s₁ s₂ : stream A} :
        head s₁ = head s₂ → (∀ (B : Type.{l}) (fr : stream A → B), fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂)) → s₁ = s₂ :=
assume hh ht,
  eq_of_bisim
    (λ s₁ s₂, head s₁ = head s₂ ∧ ∀ (B : Type) (fr : stream A → B), fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂))
    (λ s₁ s₂ h,
      have h₁ : head s₁ = head s₂,               from and.elim_left h,
      have h₂ : head (tail s₁) = head (tail s₂), from and.elim_right h A (@head A) h₁,
      have h₃ : ∀ (B : Type) (fr : stream A → B), fr (tail s₁) = fr (tail s₂) → fr (tail (tail s₁)) = fr (tail (tail s₂)), from
        λ B fr, and.elim_right h B (λ s, fr (tail s)),
      and.intro h₁ (and.intro h₂ h₃))
    (and.intro hh ht)

theorem iterate_id (a : A) : iterate id a = const a :=
coinduction
  rfl
  (λ B fr ch, by rewrite [tail_iterate, tail_const]; exact ch)


local attribute stream [reducible]
theorem map_iterate (f : A → A) (a : A) : iterate f (f a) = map f (iterate f a) :=
begin
  apply funext, intro n,
  induction n with n' IH,
    {reflexivity},
    { esimp [map, iterate, nth] at *,
      rewrite IH }
end

section corec
  definition corec (f : A → B) (g : A → A) : A → stream B :=
  λ a, map f (iterate g a)

  theorem corec_def (f : A → B) (g : A → A) (a : A) : corec f g a = map f (iterate g a) :=
  rfl

  theorem corec_eq (f : A → B) (g : A → A) (a : A) : corec f g a = f a :: corec f g (g a) :=
  by rewrite [corec_def, map_eq, head_iterate, tail_iterate]

  theorem corec_id_id_eq_const (a : A) : corec id id a = const a :=
  by rewrite [corec_def, map_id, iterate_id]

  theorem corec_id_f_eq_iterate (f : A → A) (a : A) : corec id f a = iterate f a :=
  rfl
end corec

-- corec is also known as unfold
definition unfolds (g : A → B) (f : A → A) (a : A) : stream B :=
corec g f a

theorem unfolds_eq (g : A → B) (f : A → A) (a : A) : unfolds g f a = g a :: unfolds g f (f a) :=
by esimp [ unfolds ]; rewrite [corec_eq]

theorem nth_unfolds_head_tail : ∀ (n : nat) (s : stream A), nth n (unfolds head tail s) = nth n s :=
begin
  intro n, induction n with n' ih,
   {intro s, reflexivity},
   {intro s, rewrite [*nth_succ, unfolds_eq, tail_cons, ih]}
end

theorem unfolds_head_eq : ∀ (s : stream A), unfolds head tail s = s :=
λ s, stream.ext (λ n, nth_unfolds_head_tail n s)

definition interleave (s₁ s₂ : stream A) : stream A :=
corec
  (λ p, obtain s₁ s₂, from p, head s₁)
  (λ p, obtain s₁ s₂, from p, (s₂, tail s₁))
  (s₁, s₂)

infix `⋈`:65 := interleave

theorem interleave_eq (s₁ s₂ : stream A) : s₁ ⋈ s₂ = head s₁ :: head s₂ :: (tail s₁ ⋈ tail s₂) :=
begin
  esimp [interleave], rewrite corec_eq, esimp, congruence, rewrite corec_eq
end

theorem tail_interleave (s₁ s₂ : stream A) : tail (s₁ ⋈ s₂) = s₂ ⋈ (tail s₁) :=
by esimp [interleave]; rewrite corec_eq

theorem interleave_tail_tail (s₁ s₂ : stream A) : tail s₁ ⋈ tail s₂ = tail (tail (s₁ ⋈ s₂)) :=
by rewrite [interleave_eq s₁ s₂]

theorem nth_interleave_left : ∀ (n : nat) (s₁ s₂ : stream A), nth (2*n) (s₁ ⋈ s₂) = nth n s₁
| 0        s₁ s₂ := rfl
| (succ n) s₁ s₂ :=
  begin
    change nth (succ (succ (2*n))) (s₁ ⋈ s₂) = nth (succ n) s₁,
    rewrite [*nth_succ, interleave_eq, *tail_cons, nth_interleave_left]
  end

theorem nth_interleave_right : ∀ (n : nat) (s₁ s₂ : stream A), nth (2*n+1) (s₁ ⋈ s₂) = nth n s₂
| 0        s₁ s₂ := rfl
| (succ n) s₁ s₂ :=
  begin
    change nth (succ (succ (2*n+1))) (s₁ ⋈ s₂) = nth (succ n) s₂,
    rewrite [*nth_succ, interleave_eq, *tail_cons, nth_interleave_right]
  end

theorem mem_interleave_left {a : A} {s₁ : stream A} (s₂ : stream A) : a ∈ s₁ → a ∈ s₁ ⋈ s₂ :=
assume ains₁, obtain n h, from ains₁,
exists.intro (2*n) (by rewrite [h, nth_interleave_left])

theorem mem_interleave_right {a : A} {s₁ : stream A} (s₂ : stream A) : a ∈ s₂ → a ∈ s₁ ⋈ s₂ :=
assume ains₂, obtain n h, from ains₂,
exists.intro (2*n+1) (by rewrite [h, nth_interleave_right])

definition even (s : stream A) : stream A :=
corec
  (λ s, head s)
  (λ s, tail (tail s))
  s

definition odd (s : stream A) : stream A :=
even (tail s)

theorem odd_eq (s : stream A) : odd s = even (tail s) :=
rfl

theorem head_even (s : stream A) : head (even s) = head s :=
rfl

theorem tail_even (s : stream A) : tail (even s) = even (tail (tail s)) :=
by esimp [even]; rewrite corec_eq

theorem even_cons_cons (a₁ a₂ : A) (s : stream A) : even (a₁ :: a₂ :: s) = a₁ :: even s :=
by esimp [even]; rewrite corec_eq

theorem even_tail (s : stream A) : even (tail s) = odd s :=
rfl

theorem even_interleave (s₁ s₂ : stream A) : even (s₁ ⋈ s₂) = s₁ :=
eq_of_bisim
  (λ s₁' s₁, ∃ s₂, s₁' = even (s₁ ⋈ s₂))
  (λ s₁' s₁ h,
    obtain s₂ (h₁ : s₁' = even (s₁ ⋈ s₂)), from h,
    begin
      rewrite h₁,
      constructor,
       {reflexivity},
       {existsi (tail s₂),
        rewrite [interleave_eq, even_cons_cons, tail_cons]}
    end)
  (exists.intro s₂ rfl)

theorem interleave_even_odd (s₁ : stream A) : even s₁ ⋈ odd s₁ = s₁ :=
eq_of_bisim
  (λ s' s, s' = even s ⋈ odd s)
  (λ s' s (h : s' = even s ⋈ odd s),
    begin
      rewrite h, constructor,
       {reflexivity},
       {esimp, rewrite [*odd_eq, tail_interleave, tail_even]}
    end)
  rfl

theorem nth_even : ∀ (n : nat) (s : stream A), nth n (even s) = nth (2*n) s
| 0        s := rfl
| (succ n) s :=
  begin
    change nth (succ n) (even s) = nth (succ (succ (2 * n))) s,
    rewrite [+nth_succ, tail_even, nth_even]
  end

theorem nth_odd : ∀ (n : nat) (s : stream A), nth n (odd s) = nth (2*n + 1) s :=
λ n s, by rewrite [odd_eq, nth_even]

theorem mem_of_mem_even (a : A) (s : stream A) : a ∈ even s → a ∈ s :=
assume aines, obtain n h, from aines,
exists.intro (2*n) (by rewrite [h, nth_even])

theorem mem_of_mem_odd (a : A) (s : stream A) : a ∈ odd s → a ∈ s :=
assume ainos, obtain n h, from ainos,
exists.intro (2*n+1) (by rewrite [h, nth_odd])

open list
definition append : list A → stream A → stream A
| []     s := s
| (a::l) s := a :: append l s

theorem nil_append (s : stream A) : append [] s = s :=
rfl

theorem cons_append (a : A) (l : list A) (s : stream A) : append (a::l) s = a :: append l s :=
rfl

infix ++ := append
-- the following local notation is used just to make the following theorem clear
local infix `++ₛ`:65 := append

theorem append_append : ∀ (l₁ l₂ : list A) (s : stream A), (l₁ ++ l₂) ++ₛ s = l₁ ++ (l₂ ++ₛ s)
| []      l₂ s := rfl
| (a::l₁) l₂ s := by rewrite [list.append_cons, *cons_append, append_append]

theorem map_append (f : A → B) : ∀ (l : list A) (s : stream A), map f (l ++ s) = list.map f l ++ map f s
| []     s := rfl
| (a::l) s := by rewrite [cons_append, list.map_cons, map_cons, cons_append, map_append]

theorem drop_append : ∀ (l : list A) (s : stream A), drop (length l) (l ++ s) = s
| []     s := by esimp
| (a::l) s := by rewrite [length_cons, add_one, drop_succ, cons_append, tail_cons, drop_append]

theorem append_head_tail (s : stream A) : [head s] ++ tail s = s :=
by rewrite [cons_append, nil_append, stream.eta]

theorem mem_append_right : ∀ {a : A} (l : list A) {s : stream A}, a ∈ s → a ∈ l ++ s
| a []     s h := h
| a (b::l) s h :=
  have ih : a ∈ l ++ s, from mem_append_right l h,
  !mem_cons_of_mem ih

theorem mem_append_left : ∀ {a : A} {l : list A} (s : stream A), a ∈ l → a ∈ l ++ s
| a []     s h := absurd h !not_mem_nil
| a (b::l) s h :=
  or.elim (list.eq_or_mem_of_mem_cons h)
    (λ (aeqb : a = b), exists.intro 0 aeqb)
    (λ (ainl : a ∈ l), mem_cons_of_mem b (mem_append_left s ainl))

definition approx : nat → stream A → list A
| 0     s := []
| (n+1) s := head s :: approx n (tail s)

theorem approx_zero (s : stream A) : approx 0 s = [] :=
rfl

theorem approx_succ (n : nat) (s : stream A) : approx (succ n) s = head s :: approx n (tail s) :=
rfl

theorem nth_approx : ∀ (n : nat) (s : stream A), list.nth (approx (succ n) s) n = some (nth n s)
| 0     s := rfl
| (n+1) s := begin rewrite [approx_succ, add_one, list.nth_succ, nth_approx] end

theorem append_approx_drop : ∀ (n : nat) (s : stream A), append (approx n s) (drop n s) = s :=
begin
  intro n,
  induction n with n' ih,
   {intro s, reflexivity},
   {intro s, rewrite [approx_succ, drop_succ, cons_append, ih (tail s), stream.eta]}
end

-- Take lemma reduces a proof of equality of infinite streams to an
-- induction over all their finite approximations.
theorem take_lemma (s₁ s₂ : stream A) : (∀ (n : nat), approx n s₁ = approx n s₂) → s₁ = s₂ :=
begin
  intro h, apply stream.ext, intro n,
    induction n with n ih,
     {injection (h 1), assumption},
     {have h₁ : some (nth (succ n) s₁) = some (nth (succ n) s₂), by rewrite [-*nth_approx, h (succ (succ n))],
      injection h₁, assumption}
end

-- auxiliary definition for cycle corecursive definition
private definition cycle_f : A × list A × A × list A → A
| (v, _, _, _) := v

-- auxiliary definition for cycle corecursive definition
private definition cycle_g : A × list A × A × list A → A × list A × A × list A
| (v₁, [],     v₀, l₀) := (v₀, l₀, v₀, l₀)
| (v₁, v₂::l₂, v₀, l₀) := (v₂, l₂, v₀, l₀)

private lemma cycle_g_cons (a : A) (a₁ : A) (l₁ : list A) (a₀ : A) (l₀ : list A) :
              cycle_g (a, a₁::l₁, a₀, l₀) = (a₁, l₁, a₀, l₀) :=
rfl

definition cycle : Π (l : list A), l ≠ nil → stream A
| []     h := absurd rfl h
| (a::l) h := corec cycle_f cycle_g (a, l, a, l)

theorem cycle_eq : ∀ (l : list A) (h : l ≠ nil), cycle l h = l ++ cycle l h
| []     h := absurd rfl h
| (a::l) h :=
  have gen : ∀ l' a', corec cycle_f cycle_g (a', l', a, l) = (a' :: l') ++ₛ corec cycle_f cycle_g (a, l, a, l),
    begin
      intro l',
      induction l' with a₁ l₁ ih,
        {intro a', rewrite [corec_eq]},
        {intro a', rewrite [corec_eq, cycle_g_cons, ih a₁]}
    end,
  gen l a

theorem mem_cycle {a : A} {l : list A} : ∀ (h : l ≠ []), a ∈ l → a ∈ cycle l h :=
assume h ainl, by rewrite [cycle_eq]; exact !mem_append_left ainl

theorem cycle_singleton (a : A) (h : [a] ≠ nil) : cycle [a] h = const a :=
coinduction
  rfl
  (λ B fr ch, by rewrite [cycle_eq, const_eq]; exact ch)

definition tails (s : stream A) : stream (stream A) :=
corec id tail (tail s)

theorem tails_eq (s : stream A) : tails s = tail s :: tails (tail s) :=
by esimp [tails]; rewrite [corec_eq]

theorem nth_tails : ∀ (n : nat) (s : stream A), nth n (tails s) = drop n (tail s) :=
begin
  intro n, induction n with n' ih,
    {intros, reflexivity},
    {intro s, rewrite [nth_succ, drop_succ, tails_eq, tail_cons, ih]}
end

theorem tails_eq_iterate (s : stream A) : tails s = iterate tail (tail s) :=
rfl

definition inits_core (l : list A) (s : stream A) : stream (list A) :=
corec
  prod.pr1
  (λ p, match p with (l', s') := (l' ++ [head s'], tail s') end)
  (l, s)

definition inits (s : stream A) : stream (list A) :=
inits_core [head s] (tail s)

theorem inits_core_eq (l : list A) (s : stream A) : inits_core l s = l :: inits_core (l ++ [head s]) (tail s) :=
by esimp [inits_core]; rewrite [corec_eq]

theorem tail_inits (s : stream A) : tail (inits s) = inits_core [head s, head (tail s)] (tail (tail s)) :=
by esimp [inits]; rewrite inits_core_eq

theorem inits_tail (s : stream A) : inits (tail s) = inits_core [head (tail s)] (tail (tail s)) :=
rfl

theorem cons_nth_inits_core : ∀ (a : A) (n : nat) (l : list A) (s : stream A),
                                 a :: nth n (inits_core l s) = nth n (inits_core (a::l) s) :=
begin
  intro a n,
  induction n with n' ih,
   {intros, reflexivity},
   {intro l s, rewrite [*nth_succ, inits_core_eq, +tail_cons, ih, inits_core_eq (a::l) s] }
end

theorem nth_inits : ∀ (n : nat) (s : stream A), nth n (inits s) = approx (succ n) s  :=
begin
  intro n, induction n with n' ih,
    {intros, reflexivity},
    {intros, rewrite [nth_succ, approx_succ, -ih, tail_inits, inits_tail, cons_nth_inits_core]}
end

theorem inits_eq (s : stream A) : inits s = [head s] :: map (list.cons (head s)) (inits (tail s)) :=
begin
  apply stream.ext, intro n,
  cases n,
    {reflexivity},
    {rewrite [nth_inits, nth_succ, tail_cons, nth_map, nth_inits]}
end

theorem zip_inits_tails (s : stream A) : zip append (inits s) (tails s) = const s :=
begin
  apply stream.ext, intro n,
  rewrite [nth_zip, nth_inits, nth_tails, nth_const, approx_succ,
           cons_append, append_approx_drop, stream.eta]
end

definition pure (a : A) : stream A :=
const a

definition apply (f : stream (A → B)) (s : stream A) : stream B :=
λ n, (nth n f) (nth n s)

infix `⊛`:75 := apply  -- input as \o*

theorem identity (s : stream A) : pure id ⊛ s = s :=
rfl
theorem composition (g : stream (B → C)) (f : stream (A → B)) (s : stream A) : pure compose ⊛ g ⊛ f ⊛ s = g ⊛ (f ⊛ s) :=
rfl
theorem homomorphism (f : A → B) (a : A) : pure f ⊛ pure a = pure (f a) :=
rfl
theorem interchange (fs : stream (A → B)) (a : A) : fs ⊛ pure a = pure (λ f, f a) ⊛ fs :=
rfl
theorem map_eq_apply (f : A → B) (s : stream A) : map f s = pure f ⊛ s :=
rfl

definition nats : stream nat :=
λ n, n

theorem nth_nats (n : nat) : nth n nats = n :=
rfl

theorem nats_eq : nats = 0 :: map succ nats :=
begin
  apply stream.ext, intro n,
  cases n, reflexivity, rewrite [nth_succ]
end

section
open equiv
lemma stream_equiv_of_equiv {A B : Type} : A ≃ B → stream A ≃ stream B
| (mk f g l r) :=
  mk (map f) (map g)
   begin intros, rewrite [map_map, id_of_left_inverse l, map_id] end
   begin intros, rewrite [map_map, id_of_righ_inverse r, map_id] end
end

definition lex (lt : A → A → Prop) (s₁ s₂ : stream A) : Prop :=
∃ i, lt (nth i s₁) (nth i s₂) ∧ ∀ j, j < i → nth j s₁ = nth j s₂

definition lex.trans {s₁ s₂ s₃} {lt : A → A → Prop} : transitive lt → lex lt s₁ s₂ → lex lt s₂ s₃ → lex lt s₁ s₃ :=
assume htrans h₁ h₂,
obtain i₁ hlt₁ he₁, from h₁,
obtain i₂ hlt₂ he₂, from h₂,
lt.by_cases
  (λ i₁lti₂ : i₁ < i₂,
    assert aux : nth i₁ s₂ = nth i₁ s₃, from he₂ _ i₁lti₂,
    begin
      existsi i₁, split,
       {rewrite -aux, exact hlt₁},
       {intro j jlti₁, transitivity nth j s₂,
         exact !he₁ jlti₁,
         exact !he₂ (lt.trans jlti₁ i₁lti₂)}
    end)
  (λ i₁eqi₂ : i₁ = i₂,
    begin
      subst i₂, existsi i₁, split, exact htrans hlt₁ hlt₂, intro j jlti₁,
        transitivity nth j s₂,
          exact !he₁ jlti₁;
          exact !he₂ jlti₁
    end)
  (λ i₂lti₁ : i₂ < i₁,
    assert nth i₂ s₁ = nth i₂ s₂, from he₁ _ i₂lti₁,
    begin
      existsi i₂, split,
       {rewrite this, exact hlt₂},
       {intro j jlti₂, transitivity nth j s₂,
         exact !he₁ (lt.trans jlti₂ i₂lti₁),
         exact !he₂ jlti₂}
    end)
end stream
