/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: hit.trunc
Authors: Floris van Doorn

n-truncation of types.

Ported from Coq HoTT
-/

/- The hit n-truncation is primitive, declared in init.hit. -/

import types.sigma

open is_trunc eq equiv is_equiv function prod sum sigma

namespace trunc

  protected definition elim {n : trunc_index} {A : Type} {P : Type}
    [Pt : is_trunc n P] (H : A → P) : trunc n A → P :=
  trunc.rec H

  protected definition elim_on {n : trunc_index} {A : Type} {P : Type} (aa : trunc n A)
    [Pt : is_trunc n P] (H : A → P) : P :=
  elim H aa

  /-
    there are no theorems to eliminate to the universe here,
    because the universe is generally not a set
  -/

end trunc
