/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about the universe
-/

-- see also init.ua

import .bool .trunc .lift

open is_trunc bool lift unit

namespace univ

  definition not_is_hset_type0 : ¬is_hset Type₀ :=
  assume H : is_hset Type₀,
  absurd !is_hset.elim eq_bnot_ne_idp

  definition not_is_hset_type.{u} : ¬is_hset Type.{u} :=
  assume H : is_hset Type,
  absurd (is_trunc_is_embedding_closed lift star) not_is_hset_type0


end univ
