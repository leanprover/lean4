-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic
using eq_proofs

namespace binary
section
  parameter {A : Type}
  parameter f : A → A → A
  infixl `*`:75 := f

  abbreviation commutative := ∀a b, a*b = b*a
  abbreviation associative := ∀a b c, (a*b)*c = a*(b*c)
end

section
  parameter {A : Type}
  parameter {f : A → A → A}
  infixl `*`:75 := f
  hypothesis H_comm : commutative f
  hypothesis H_assoc : associative f

  theorem left_comm : ∀a b c, a*(b*c) = b*(a*c) :=
  take a b c, calc
    a*(b*c) = (a*b)*c  : (H_assoc _ _ _)⁻¹
      ...   = (b*a)*c  : {H_comm _ _}
      ...   = b*(a*c)  : H_assoc _ _ _

  theorem right_comm : ∀a b c, (a*b)*c = (a*c)*b :=
  take a b c, calc
    (a*b)*c = a*(b*c) : H_assoc _ _ _
      ...   = a*(c*b) : {H_comm _ _}
      ...   = (a*c)*b : (H_assoc _ _ _)⁻¹
end
end
