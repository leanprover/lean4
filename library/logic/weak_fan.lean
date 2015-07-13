/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

This file is based on Coq's WeakFan.v file

A constructive proof of a non-standard version of the weak Fan Theorem
in the formulation of which infinite paths are treated as
predicates. The representation of paths as relations avoid the
need for classical logic and unique choice. The idea of the proof
comes from the proof of the weak König's lemma from separation in
second-order arithmetic:

    Stephen G. Simpson. Subsystems of second order
    arithmetic, Cambridge University Press, 1999
-/
import data.list
open bool nat list

namespace weak_fan
-- inductively_barred P l means that P eventually holds above l
inductive inductively_barred (P : list bool → Prop) : list bool → Prop :=
| base      : ∀ l, P l → inductively_barred P l
| propagate : ∀ l,
    inductively_barred P (tt::l) →
    inductively_barred P (ff::l) →
    inductively_barred P l

-- approx X l says that l is a boolean representation of a prefix of X
definition approx : (nat → Prop) → (list bool) → Prop
| X []     := true
| X (b::l) := approx X l ∧ (cond b (X (length l)) (¬ (X (length l))))

-- barred P means that for any infinite path represented as a predicate, the property P holds for some prefix of the path
definition barred P := ∀ X, ∃ l, approx X l ∧ P l

/-
The proof proceeds by building a set Y of finite paths
approximating either the smallest unbarred infinite path in P, if
there is one (taking tt > ff), or the path tt::tt::...
if P happens to be inductively_barred
-/
private definition Y : (list bool → Prop) → list bool → Prop
| P []     := true
| P (b::l) := Y P l ∧ (cond b (inductively_barred P (ff::l)) (¬(inductively_barred P (ff::l))))

private lemma Y_unique : ∀ {P l₁ l₂}, length l₁ = length l₂ → Y P l₁ → Y P l₂ → l₁ = l₂
| P []       []       h₁ h₂ h₃ := rfl
| P []       (a₂::l₂) h₁ h₂ h₃ := by contradiction
| P (a₁::l₁) []       h₁ h₂ h₃ := by contradiction
| P (a₁::l₁) (a₂::l₂) h₁ h₂ h₃ :=
  have n₁ : length l₁ = length l₂, by rewrite [*length_cons at h₁]; apply add.cancel_right h₁,
  have n₂ : Y P l₁,  from and.elim_left h₂,
  have n₃ : Y P l₂,  from and.elim_left h₃,
  assert ih : l₁ = l₂, from Y_unique n₁ n₂ n₃,
  begin
    clear Y_unique, subst l₂, congruence,
    show a₁ = a₂,
    begin
      cases a₁,
        {cases a₂, reflexivity, exact absurd (and.elim_right h₃) (and.elim_right h₂)},
        {cases a₂, exact absurd (and.elim_right h₂) (and.elim_right h₃), reflexivity}
    end
  end

-- X is the translation of Y as a predicate
private definition X P n := ∃ l, length l = n ∧ Y P (tt::l)

private lemma Y_approx : ∀ {P l}, approx (X P) l → Y P l
| P []     h := trivial
| P (a::l) h :=
  begin
    have ypl : Y P l, from Y_approx (and.elim_left h),
    unfold Y, split,
     {exact ypl},
     {cases a,
       {have nxp : ¬X P (length l), begin unfold approx at h, rewrite cond_ff at h, exact and.elim_right h end,
        rewrite cond_ff, intro ib,
        have xp  : X P (length l), begin existsi l, split, reflexivity, unfold Y, split, exact ypl, rewrite cond_tt, exact ib end,
        contradiction},
       {rewrite cond_tt,
        have xp : X P (length l), begin unfold approx at h, rewrite cond_tt at h, exact and.elim_right h end,
        obtain l₁ hl yptt, from xp,
        begin
          unfold Y at yptt, rewrite cond_tt at yptt,
          have ypl₁ : Y P l₁,                        from and.elim_left yptt,
          have ib₁  : inductively_barred P (ff::l₁), from and.elim_right yptt,
          have ll₁  : l₁ = l,                        from Y_unique hl ypl₁ ypl,
          subst l, exact ib₁
        end}}
  end

theorem weak_fan : ∀ {P}, barred P → inductively_barred P [] :=
λ P Hbar,
obtain l Hd HP, from Hbar (X P),
assert ib : inductively_barred P l, from inductively_barred.base l HP,
begin
  clear Hbar HP,
  induction l with a l ih,
    {exact ib},
    {unfold approx at Hd, cases Hd with Hd HX,
     have ypl : Y P l, from Y_approx Hd,
     cases a,
       {rewrite cond_ff at HX,
        have xpl : X P (length l), begin unfold X, existsi l, split, reflexivity, unfold Y, rewrite cond_tt, split, repeat assumption end,
        exact absurd xpl HX},
       {rewrite cond_tt at HX,
        obtain l₁ hl yptt, from HX,
        begin
          unfold Y at yptt, rewrite cond_tt at yptt,
          have ll₁ : l₁ = l, from Y_unique hl (and.elim_left yptt) ypl,
          subst l₁,
          have ibl : inductively_barred P l, from inductively_barred.propagate l ib (and.elim_right yptt),
          exact ih Hd ibl,
        end}}
end
end weak_fan
