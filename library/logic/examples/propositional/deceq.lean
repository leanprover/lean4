/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura

PropF has decidable equality
-/
import .soundness
open bool decidable nat

namespace PropF
  -- Show that PropF has decidable equality

  definition equal : PropF → PropF → bool
  | (Var x) (Var y)           := if x = y then tt else ff
  | Bot Bot                   := tt
  | (Conj p₁ p₂) (Conj q₁ q₂) := equal p₁ q₁ && equal p₂ q₂
  | (Disj p₁ p₂) (Disj q₁ q₂) := equal p₁ q₁ && equal p₂ q₂
  | (Impl p₁ p₂) (Impl q₁ q₂) := equal p₁ q₁ && equal p₂ q₂
  | _            _            := ff

  lemma equal_refl : ∀ p, equal p p = tt
  | (Var x)      := if_pos rfl
  | Bot          := rfl
  | (Conj p₁ p₂) := begin change (equal p₁ p₁ && equal p₂ p₂ = tt), rewrite *equal_refl end
  | (Disj p₁ p₂) := begin change (equal p₁ p₁ && equal p₂ p₂ = tt), rewrite *equal_refl end
  | (Impl p₁ p₂) := begin change (equal p₁ p₁ && equal p₂ p₂ = tt), rewrite *equal_refl end

  lemma equal_to_eq : ∀ ⦃p q⦄, equal p q = tt → p = q
  | (Var x) (Var y) H :=
    if H₁ : x = y then congr_arg Var H₁
    else by rewrite [▸ (if x = y then tt else ff) = tt at H, if_neg H₁ at H]; exact (absurd H ff_ne_tt)
  | Bot Bot H  := rfl
  | (Conj p₁ p₂) (Conj q₁ q₂) H :=
    by rewrite [equal_to_eq (band_elim_left H), equal_to_eq (band_elim_right H)]
  | (Disj p₁ p₂) (Disj q₁ q₂) H :=
    by rewrite [equal_to_eq (band_elim_left H), equal_to_eq (band_elim_right H)]
  | (Impl p₁ p₂) (Impl q₁ q₂) H :=
    by rewrite [equal_to_eq (band_elim_left H), equal_to_eq (band_elim_right H)]

  lemma has_decidable_eq [instance] : decidable_eq PropF :=
  decidable_eq_of_bool_pred equal_to_eq equal_refl
end PropF
