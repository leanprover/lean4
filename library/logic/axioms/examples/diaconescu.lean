/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/

import logic.axioms.hilbert logic.eq
open eq.ops

/-
Diaconescu’s theorem: excluded middle follows from Hilbert's choice operator, function extensionality,
  and Prop extensionality
-/

section
parameter  p : Prop

private definition U (x : Prop) : Prop := x = true ∨ p
private definition V (x : Prop) : Prop := x = false ∨ p

private noncomputable definition u := epsilon U
private noncomputable definition v := epsilon V

private lemma u_def : U u :=
epsilon_spec (exists.intro true (or.inl rfl))

private lemma v_def : V v :=
epsilon_spec (exists.intro false (or.inl rfl))

private lemma not_uv_or_p : ¬(u = v) ∨ p :=
or.elim u_def
  (assume Hut : u = true,
    or.elim v_def
      (assume Hvf : v = false,
        have Hne : ¬(u = v), from Hvf⁻¹ ▸ Hut⁻¹ ▸ true_ne_false,
        or.inl Hne)
      (assume Hp : p, or.inr Hp))
  (assume Hp : p, or.inr Hp)

private lemma p_implies_uv : p → u = v :=
assume Hp : p,
have Hpred : U = V, from
  funext (take x : Prop,
    have Hl : (x = true ∨ p) → (x = false ∨ p), from
      assume A, or.inr Hp,
    have Hr : (x = false ∨ p) → (x = true ∨ p), from
      assume A, or.inr Hp,
    show (x = true ∨ p) = (x = false ∨ p), from
      propext (iff.intro Hl Hr)),
have H' : epsilon U = epsilon V, from Hpred ▸ rfl,
show u = v, from H'

theorem em : p ∨ ¬p :=
have H : ¬(u = v) → ¬p, from mt p_implies_uv,
  or.elim not_uv_or_p
    (assume Hne : ¬(u = v), or.inr (H Hne))
    (assume Hp : p, or.inl Hp)
end
