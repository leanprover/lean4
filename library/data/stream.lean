/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import data.nat
open nat

definition stream (A : Type) := nat → A

namespace stream
variables {A B C : Type}

definition cons (a : A) (s : stream A) : stream A :=
λ i,
  match i with
  | 0      := a
  | succ n := s n
  end

definition head (s : stream A) : A :=
s 0

definition tail (s : stream A) : stream A :=
λ i, s (i+1)

definition nth_tail (n : nat) (s : stream A) : stream A :=
λ i, s (i+n)

definition nth (n : nat) (s : stream A) : A :=
s n

protected theorem eta (s : stream A) : cons (head s) (tail s) = s :=
funext (λ i, begin cases i, repeat reflexivity end)

theorem tail_nth_tail (n : nat) (s : stream A) : tail (nth_tail n s) = nth_tail n (tail s) :=
funext (λ i, begin esimp [tail, nth_tail], congruence, rewrite add.right_comm end)

theorem nth_nth_tail (n m : nat) (s : stream A) : nth n (nth_tail m s) = nth (n+m) s :=
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
end map

section zip
variable (f : A → B → C)

definition zip (s₁ : stream A) (s₂ : stream B) : stream C :=
λ n, f (nth n s₁) (nth n s₂)

theorem nth_tail_zip (n : nat) (s₁ : stream A) (s₂ : stream B) : nth_tail n (zip f s₁ s₂) = zip f (nth_tail n s₁) (nth_tail n s₂) :=
stream.ext (λ i, rfl)

theorem nth_zip (n : nat) (s₁ : stream A) (s₂ : stream B) : nth n (zip f s₁ s₂) = f (nth n s₁) (nth n s₂) :=
rfl
end zip

definition repeat (a : A) : stream A :=
λ n, a

theorem nth_repeat (n : nat) (a : A) : nth n (repeat a) = a :=
rfl

theorem nth_tail_repeat (n : nat) (a : A) : nth_tail n (repeat a) = repeat a :=
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

theorem nth_zero_iterate (f : A → A) (a : A) : nth 0 (iterate f a) = a :=
rfl

theorem nth_succ_iterate (n : nat) (f : A → A) (a : A) : nth (succ n) (iterate f a) = nth n (iterate f (f a)) :=
by rewrite [nth_succ, tail_iterate]

theorem map_iterate (f : A → A) (a : A) : iterate f (f a) = map f (iterate f a) :=
begin
  apply funext, intro n,
  induction n with n' IH,
    {reflexivity},
    {esimp [map, iterate, nth] at *,
     rewrite IH}
end
end stream
