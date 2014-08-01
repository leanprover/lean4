-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Leonardo de Moura, Jeremy Avigad
import logic hilbert funext
using eq_proofs

-- Diaconescu’s theorem
-- Show that Excluded middle follows from
--   Hilbert's choice operator, function extensionality and Prop extensionality
section
hypothesis propext {a b : Prop} : (a → b) → (b → a) → a = b

parameter p : Prop

definition u [private] := epsilon (λ x, x = true ∨ p)

definition v [private] := epsilon (λ x, x = false ∨ p)

lemma u_def [private] : u = true ∨ p :=
epsilon_ax (exists_intro true (or_inl (refl true)))

lemma v_def [private] : v = false ∨ p :=
epsilon_ax (exists_intro false (or_inl (refl false)))

lemma uv_implies_p [private] : ¬(u = v) ∨ p :=
or_elim u_def
  (assume Hut : u = true, or_elim v_def
    (assume Hvf : v = false,
      have Hne : ¬(u = v), from Hvf⁻¹ ▸ Hut⁻¹ ▸ true_ne_false,
      or_inl Hne)
    (assume Hp : p, or_inr Hp))
  (assume Hp : p, or_inr Hp)

lemma p_implies_uv [private] : p → u = v :=
assume Hp : p,
  have Hpred : (λ x, x = true ∨ p) = (λ x, x = false ∨ p), from
    funext (take x : Prop,
      have Hl : (x = true ∨ p) → (x = false ∨ p), from
        assume A, or_inr Hp,
      have Hr : (x = false ∨ p) → (x = true ∨ p), from
        assume A, or_inr Hp,
      show (x = true ∨ p) = (x = false ∨ p), from
        propext Hl Hr),
  show u = v, from
    Hpred ▸ (refl (epsilon (λ x, x = true ∨ p)))

theorem em : p ∨ ¬p :=
have H : ¬(u = v) → ¬p, from contrapos p_implies_uv,
  or_elim uv_implies_p
    (assume Hne : ¬(u = v), or_inr (H Hne))
    (assume Hp : p, or_inl Hp)
end
