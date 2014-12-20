/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura, Jeremy Avigad
-/
prelude
import init.datatypes init.reserved_notation

namespace sum
  notation A ⊎ B := sum A B
  notation A + B := sum A B
  namespace low_precedence_plus
    reserve infixr `+`:25  -- conflicts with notation for addition
    infixr `+` := sum
  end low_precedence_plus
end sum
