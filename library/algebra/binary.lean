-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic.core.eq
open eq_ops

namespace binary
  context
    parameter {A : Type}
    parameter f : A → A → A
    infixl `*`:75 := f
    abbreviation commutative := ∀{a b}, a*b = b*a
    abbreviation associative := ∀{a b c}, (a*b)*c = a*(b*c)
  end

  context
    parameter {A : Type}
    parameter {f : A → A → A}
    hypothesis H_comm : commutative f
    hypothesis H_assoc : associative f
    infixl `*`:75 := f
    theorem left_comm : ∀a b c, a*(b*c) = b*(a*c) :=
    take a b c, calc
      a*(b*c) = (a*b)*c  : H_assoc⁻¹
        ...   = (b*a)*c  : {H_comm}
        ...   = b*(a*c)  : H_assoc

    theorem right_comm : ∀a b c, (a*b)*c = (a*c)*b :=
    take a b c, calc
      (a*b)*c = a*(b*c) : H_assoc
        ...   = a*(c*b) : {H_comm}
        ...   = (a*c)*b : H_assoc⁻¹
  end
end binary
