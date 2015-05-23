/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import data.nat algebra.function
open nat function

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

definition head (s : stream A) : A :=
s 0

definition tail (s : stream A) : stream A :=
λ i, s (i+1)

definition nth_tail (n : nat) (s : stream A) : stream A :=
λ i, s (i+n)

definition nth (n : nat) (s : stream A) : A :=
s n

protected theorem eta (s : stream A) : head s :: tail s = s :=
funext (λ i, begin cases i, repeat reflexivity end)

theorem head_cons (a : A) (s : stream A) : head (a :: s) = a :=
rfl

theorem tail_cons (a : A) (s : stream A) : tail (a :: s) = s :=
rfl

theorem tail_nth_tail (n : nat) (s : stream A) : tail (nth_tail n s) = nth_tail n (tail s) :=
funext (λ i, begin esimp [tail, nth_tail], congruence, rewrite add.right_comm end)

theorem nth_nth_tail (n m : nat) (s : stream A) : nth n (nth_tail m s) = nth (n+m) s :=
rfl

theorem tail_eq_nth_tail (s : stream A) : tail s = nth_tail 1 s :=
rfl

theorem nth_tail_nth_tail (n m : nat) (s : stream A) : nth_tail n (nth_tail m s) = nth_tail (n+m) s :=
funext (λ i, begin esimp [nth_tail], rewrite add.assoc end)

theorem nth_succ (n : nat) (s : stream A) : nth (succ n) s = nth n (tail s) :=
rfl

protected theorem ext {s₁ s₂ : stream A} : (∀ n, nth n s₁ = nth n s₂) → s₁ = s₂ :=
assume h, funext h

protected definition all (p : A → Prop) (s : stream A) := ∀ n, p (nth n s)

protected definition any (p : A → Prop) (s : stream A) := ∃ n, p (nth n s)

theorem all_def (p : A → Prop) (s : stream A) : stream.all p s = ∀ n, p (nth n s) :=
rfl

theorem any_def (p : A → Prop) (s : stream A) : stream.any p s = ∃ n, p (nth n s) :=
rfl

section map
variable (f : A → B)

definition map (s : stream A) : stream B :=
λ n, f (nth n s)

theorem nth_tail_map (n : nat) (s : stream A) : nth_tail n (map f s) = map f (nth_tail n s) :=
stream.ext (λ i, rfl)

theorem nth_map (n : nat) (s : stream A) : nth n (map f s) = f (nth n s) :=
rfl

theorem tail_map (s : stream A) : tail (map f s) = map f (tail s) :=
begin rewrite tail_eq_nth_tail end

theorem head_map (s : stream A) : head (map f s) = f (head s) :=
rfl

theorem map_eq (s : stream A) : map f s = f (head s) :: map f (tail s) :=
by rewrite [-stream.eta, tail_map, head_map]

theorem map_id (s : stream A) : map id s = s :=
rfl
end map

section zip
variable (f : A → B → C)

definition zip (s₁ : stream A) (s₂ : stream B) : stream C :=
λ n, f (nth n s₁) (nth n s₂)

theorem nth_tail_zip (n : nat) (s₁ : stream A) (s₂ : stream B) : nth_tail n (zip f s₁ s₂) = zip f (nth_tail n s₁) (nth_tail n s₂) :=
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

theorem nth_tail_const (n : nat) (a : A) : nth_tail n (const a) = const a :=
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
  definition is_bisimulation (R : stream A → stream A → Prop) := ∀ ⦃s₁ s₂⦄, R s₁ s₂ → head s₁ = head s₂ ∧ R (tail s₁) (tail s₂)

  variable {R : stream A → stream A → Prop}
  local infix ~ := R

  lemma nth_of_bisim (bisim : is_bisimulation R) : ∀ {s₁ s₂} n, s₁ ~ s₂ → nth n s₁ = nth n s₂ ∧ nth_tail (n+1) s₁ ~ nth_tail (n+1) s₂
  | s₁ s₂ 0     h := bisim h
  | s₁ s₂ (n+1) h :=
    obtain h₁ (trel : tail s₁ ~ tail s₂), from bisim h,
    nth_of_bisim n trel

  -- If two streams are bisimilar, then they are equal
  theorem eq_of_bisim (bisim : is_bisimulation R) : ∀ {s₁ s₂}, s₁ ~ s₂ → s₁ = s₂ :=
  λ s₁ s₂ r, stream.ext (λ n, and.elim_left (nth_of_bisim bisim n r))
end bisim

theorem bisim_simple (s₁ s₂ : stream A) : head s₁ = head s₂ → s₁ = tail s₁ → s₂ = tail s₂ → s₁ = s₂ :=
let R := λ s₁ s₂, head s₁ = head s₂ ∧ s₁ = tail s₁ ∧ s₂ = tail s₂ in
have bisim : is_bisimulation R, from
  λ s₁ s₂ (h : R s₁ s₂),
    obtain h₁ h₂ h₃, from h,
    begin
      constructor, exact h₁, rewrite [-h₂, -h₃], exact h
    end,
assume hh ht₁ ht₂,
have Rs₁s₂ : R s₁ s₂, from and.intro hh (and.intro ht₁ ht₂),
eq_of_bisim bisim Rs₁s₂

theorem iterate_id (a : A) : iterate id a = const a :=
begin
  apply bisim_simple,
    reflexivity,
    rewrite tail_iterate,
    rewrite tail_const
end

theorem map_iterate (f : A → A) (a : A) : iterate f (f a) = map f (iterate f a) :=
begin
  apply funext, intro n,
  induction n with n' IH,
    {reflexivity},
    {esimp [map, iterate, nth] at *,
     rewrite IH}
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
end stream
