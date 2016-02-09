/-
Copyright (c) 2014-2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn, Jakob von Raumer
-/

prelude
import init.num init.relation
open iff

-- Empty type
-- ----------

protected definition empty.has_decidable_eq [instance] : decidable_eq empty :=
take (a b : empty), decidable.inl (!empty.elim a)

-- Unit type
-- ---------

namespace unit

  notation `⋆` := star

end unit

-- Sigma type
-- ----------

notation `Σ` binders `, ` r:(scoped P, sigma P) := r
abbreviation dpair [constructor] := @sigma.mk
namespace sigma
  notation `⟨`:max t:(foldr `, ` (e r, mk e r)) `⟩`:0 := t --input ⟨ ⟩ as \< \>

  namespace ops
  postfix `.1`:(max+1) := pr1
  postfix `.2`:(max+1) := pr2
  abbreviation pr₁ := @pr1
  abbreviation pr₂ := @pr2
  end ops
end sigma

-- Sum type
-- --------

namespace sum
  namespace low_precedence_plus
    reserve infixr ` + `:25  -- conflicts with notation for addition
    infixr ` + ` := sum
  end low_precedence_plus

  variables {a b c d : Type}

  definition sum_of_sum_of_imp_of_imp (H₁ : a ⊎ b) (H₂ : a → c) (H₃ : b → d) : c ⊎ d :=
  sum.rec_on H₁
    (assume Ha : a, sum.inl (H₂ Ha))
    (assume Hb : b, sum.inr (H₃ Hb))

  definition sum_of_sum_of_imp_left (H₁ : a ⊎ c) (H : a → b) : b ⊎ c :=
  sum.rec_on H₁
    (assume H₂ : a, sum.inl (H H₂))
    (assume H₂ : c, sum.inr H₂)

  definition sum_of_sum_of_imp_right (H₁ : c ⊎ a) (H : a → b) : c ⊎ b :=
  sum.rec_on H₁
    (assume H₂ : c, sum.inl H₂)
    (assume H₂ : a, sum.inr (H H₂))
end sum

-- Product type
-- ------------

namespace prod

  -- notation for n-ary tuples
  notation `(` h `, ` t:(foldl `,` (e r, prod.mk r e) h) `)` := t

  namespace ops
  postfix `.1`:(max+1) := pr1
  postfix `.2`:(max+1) := pr2
  abbreviation pr₁ := @pr1
  abbreviation pr₂ := @pr2
  end ops

  namespace low_precedence_times

    reserve infixr ` * `:30  -- conflicts with notation for multiplication
    infixr ` * ` := prod

  end low_precedence_times

  open prod.ops

  definition flip [unfold 3] {A B : Type} (a : A × B) : B × A := pair (pr2 a) (pr1 a)

end prod
