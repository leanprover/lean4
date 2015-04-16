-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura

import logic.axioms.hilbert logic.eq
open eq.ops nonempty inhabited

-- Diaconescu’s theorem
-- Show that Excluded middle follows from
--   Hilbert's choice operator, function extensionality and Prop extensionality
context
parameter  p : Prop

private definition u [reducible] := epsilon (λx, x = true ∨ p)

private definition v [reducible] := epsilon (λx, x = false ∨ p)

private lemma u_def : u = true ∨ p :=
epsilon_spec (exists.intro true (or.inl rfl))

private lemma v_def : v = false ∨ p :=
epsilon_spec (exists.intro false (or.inl rfl))

private lemma uv_implies_p : ¬(u = v) ∨ p :=
or.elim u_def
  (assume Hut : u = true, or.elim v_def
    (assume Hvf : v = false,
      have Hne : ¬(u = v), from Hvf⁻¹ ▸ Hut⁻¹ ▸ true_ne_false,
      or.inl Hne)
    (assume Hp : p, or.inr Hp))
  (assume Hp : p, or.inr Hp)

private lemma p_implies_uv : p → u = v :=
assume Hp : p,
  have Hpred : (λ x, x = true ∨ p) = (λ x, x = false ∨ p), from
    funext (take x : Prop,
      have Hl : (x = true ∨ p) → (x = false ∨ p), from
        assume A, or.inr Hp,
      have Hr : (x = false ∨ p) → (x = true ∨ p), from
        assume A, or.inr Hp,
      show (x = true ∨ p) = (x = false ∨ p), from
        propext (iff.intro Hl Hr)),
  show u = v, from
    Hpred ▸ (eq.refl (epsilon (λ x, x = true ∨ p)))

theorem em : p ∨ ¬p :=
have H : ¬(u = v) → ¬p, from mt p_implies_uv,
  or.elim uv_implies_p
    (assume Hne : ¬(u = v), or.inr (H Hne))
    (assume Hp : p, or.inl Hp)
end
