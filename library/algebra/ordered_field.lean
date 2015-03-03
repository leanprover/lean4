/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.ordered_field
Authors: Robert Lewis

Here an "ordered_ring" is partially ordered ring, which is ordered with respect to both a weak
order and an associated strict order. Our numeric structures (int, rat, and real) will be instances
of "linear_ordered_comm_ring". This development is modeled after Isabelle's library.
-/

import algebra.ordered_ring algebra.field
open eq eq.ops

namespace algebra
          
structure ordered_field [class] (A : Type) extends ordered_ring A, field A

section ordered_field
  
  variable {A : Type}
  variables [s : ordered_field A] {a b c : A}
  include s

  theorem div_pos_of_pos (H : a > 0) : 1 / a > 0 :=
    sorry

  theorem div_neg_of_neg (H : a < 0) : 1 / a < 0 :=
    sorry

  theorem le_of_div_le (H : a > 0) (Hl : 1 / a ≤ 1 / b) : b ≤ a :=
    sorry

  theorem lt_of_div_lt (H : a > 0) (Hl : 1 / a < 1 / b) : b < a :=
    sorry

  theorem le_of_div_le_neg (H : b < 0) (Hl : 1 / a ≤ 1 / b) : b ≤ a :=
    sorry

  theorem lt_of_div_lt_pos (H : b < 0) (Hl : 1 / a < 1 / b) : b < a :=
    sorry

  theorem pos_iff_div_pos : a > 0 ↔ 1 / a > 0 :=
    sorry

end ordered_field
end algebra
