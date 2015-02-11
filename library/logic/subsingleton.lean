/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: logic.subsingleton
Author: Floris van Doorn
-/

import logic.eq

inductive subsingleton [class] (A : Type) : Prop :=
intro : (∀ a b : A, a = b) → subsingleton A

namespace subsingleton
definition elim {A : Type} {H : subsingleton A} : ∀(a b : A), a = b := subsingleton.rec (fun p, p) H
end subsingleton

protected definition prop.subsingleton [instance] (P : Prop) : subsingleton P :=
subsingleton.intro (λa b, !proof_irrel)

theorem irrelevant [instance] (p : Prop) : subsingleton (decidable p) :=
subsingleton.intro (fun d1 d2,
  decidable.rec
    (assume Hp1 : p, decidable.rec
      (assume Hp2  : p,  congr_arg decidable.inl (eq.refl Hp1)) -- using proof irrelevance for Prop
      (assume Hnp2 : ¬p, absurd Hp1 Hnp2)
      d2)
    (assume Hnp1 : ¬p, decidable.rec
      (assume Hp2  : p,  absurd Hp2 Hnp1)
      (assume Hnp2 : ¬p, congr_arg decidable.inr (eq.refl Hnp1)) -- using proof irrelevance for Prop
      d2)
   d1)

protected theorem rec_subsingleton [instance] {p : Prop} [H : decidable p]
    {H1 : p → Type} {H2 : ¬p → Type}
    (H3 : Π(h : p), subsingleton (H1 h)) (H4 : Π(h : ¬p), subsingleton (H2 h))
  : subsingleton (decidable.rec_on H H1 H2) :=
decidable.rec_on H (λh, H3 h) (λh, H4 h) --this can be proven using dependent version of "by_cases"
