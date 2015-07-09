/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura

Formalization of Theorem 1 from the following paper:
"The inconsistency of a Brouwerian continuity
principle with the Curry–Howard interpretation"
by Martín Escardó and Chuangjie Xu
-/
import data.nat
open nat sigma.ops

/- Bounded equality: α and β agree in the first n positions. -/
definition beq (α β : nat → nat) (n : nat) : Prop :=
∀ a, a < n → α a = β a

notation α `=[`:50 n:50 `]` β:50 := beq α β n

lemma pred_beq {α β : nat → nat} {n : nat} : α =[n+1] β → α =[n] β :=
λ h a altn, h a (lt.step altn)

definition continuous (f : (nat → nat) → nat) : Type₁ :=
∀ α, Σ n, ∀ β, α =[n] β → f α = f β

definition zω : nat → nat :=
λ x, zero

definition znkω (n : nat) (k : nat) : nat → nat :=
λ x, if x < n then 0 else k

lemma znkω_succ (n : nat) (k : nat) : znkω (n+1) k 0 = 0 :=
rfl

lemma znkω_bound (n : nat) (k : nat) : znkω n k n = k :=
if_neg !lt.irrefl

lemma zω_eq_znkω (n : nat) (k : nat) : zω =[n] znkω n k :=
λ a altn, begin esimp [zω, znkω], rewrite [if_pos altn] end

section
hypothesis all_continuous : ∀ f, continuous f

definition M (f : (nat → nat) → nat) : nat :=
(all_continuous f zω).1

lemma M_spec (f : (nat → nat) → nat) : ∀ β, zω =[M f] β → f zω = f β :=
(all_continuous f zω).2

definition m := M (λα, zero)

definition f β :=  M (λα, β (α m))

lemma β0_eq (β : nat → nat) : ∀ α, zω =[f β] α → β 0 = β (α m) :=
λ α, M_spec (λα, β (α m)) α

lemma not_all_continuous : false :=
let β := znkω (M f + 1) 1 in
let α := znkω m (M f + 1) in
assert βeq₁ : zω =[M f + 1] β, from
  λ (a : nat) (h : a < M f + 1), begin unfold zω, unfold znkω, rewrite [if_pos h] end,
assert βeq₂    : zω =[M f] β,                    from pred_beq βeq₁,
assert m_eq_fβ : m = f β,                        from M_spec f β βeq₂,
assert aux     : ∀ α, zω =[m] α → β 0 = β (α m), by rewrite m_eq_fβ at {1}; exact (β0_eq β),
assert zero_eq_one : 0 = 1, from calc
  0   = β 0         : by rewrite znkω_succ
  ... = β (α m)     : aux α (zω_eq_znkω m (M f + 1))
  ... = β (M f + 1) : by rewrite znkω_bound
  ... = 1           : by rewrite znkω_bound,
by contradiction
end

/-
Additional remarks:
By using the slightly different definition of continuous
  ∀ α, ∃ n, ∀ β, α =[n] β → f α = f β
i.e., using ∃ instead of Σ, we can assume the following axiom
  all_continuous : ∀ f, continuous f
However, the system becomes inconsistent again if we also assume Hilbert's choice,
because with Hilbert's choice we can convert ∃ into Σ
-/
