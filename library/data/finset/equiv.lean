/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import data.finset.card
open nat nat.finset decidable

namespace finset
variable {A : Type}

private definition to_nat (s : finset nat) : nat :=
nat.finset.Sum s (λ n, 2^n)

private lemma to_nat_empty : to_nat ∅ = 0 :=
rfl

private lemma to_nat_insert {n : nat} {s : finset nat} : n ∉ s → to_nat (insert n s) = 2^n + to_nat s :=
assume h, Sum_insert_of_not_mem _ h

private definition of_nat (s : nat) : finset nat :=
{ n ∈ upto (succ s) | odd (s div 2^n) }

private lemma of_nat_zero : of_nat 0 = ∅ :=
rfl

private lemma odd_of_mem_of_nat {n : nat} {s : nat} : n ∈ of_nat s → odd (s div 2^n) :=
assume h, of_mem_sep h

private lemma mem_of_nat_of_odd {n : nat} {s : nat} : odd (s div 2^n) → n ∈ of_nat s :=
assume h,
have 2^n < succ s, from by_contradiction
  (suppose ¬(2^n < succ s),
   assert 2^n > s, from lt_of_succ_le (le_of_not_gt this),
   assert s div 2^n = 0, from div_eq_zero_of_lt this,
   by rewrite this at h; exact absurd h dec_trivial),
have n < succ s,        from calc
   n   ≤ 2^n    : le_pow_self dec_trivial n
   ... < succ s : this,
have n ∈ upto (succ s), from mem_upto_of_lt this,
mem_sep_of_mem this h

private lemma succ_mem_of_nat (n : nat) (s : nat) : succ n ∈ of_nat s ↔ n ∈ of_nat (s div 2) :=
iff.intro
  (suppose succ n ∈ of_nat s,
   assert odd (s div 2^(succ n)),    from odd_of_mem_of_nat this,
   have odd ((s div 2) div (2 ^ n)), by rewrite [pow_succ at this, div_div_eq_div_mul, mul.comm]; assumption,
   show n ∈ of_nat (s div 2),        from mem_of_nat_of_odd this)
  (suppose n ∈ of_nat (s div 2),
   assert odd ((s div 2) div (2 ^ n)), from odd_of_mem_of_nat this,
   assert odd (s div 2^(succ n)),      by rewrite [pow_succ, mul.comm, -div_div_eq_div_mul]; assumption,
   show succ n ∈ of_nat s,             from mem_of_nat_of_odd this)

/-
private lemma of_nat_to_nat (s : finset nat) : of_nat (to_nat s) = s :=
finset.induction_on s rfl
  begin
    intro n s nains ih,
    rewrite (to_nat_insert nains)
  end
-/
end finset
