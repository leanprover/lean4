/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jakob von Raumer, Floris van Doorn
-/

prelude
import init.datatypes init.reserved_notation init.tactic init.logic
import init.bool init.num init.relation init.wf
import init.types init.connectives
import init.trunc init.path init.equiv init.util
import init.ua init.funext
import init.hedberg init.nat init.hit init.pathover

namespace core
  export bool unit
  export empty (hiding elim)
  export sum (hiding elim)
  export sigma (hiding pr1 pr2)
  export [notation] prod
  export [notation] nat
  export eq (idp idpath concat inverse transport ap ap10 cast tr_inv homotopy ap11 apd refl)
  export [declaration] function
  export equiv (to_inv to_right_inv to_left_inv)
  export is_equiv (inv right_inv left_inv adjointify)
  export [abbreviation] [declaration] is_trunc (Prop.mk Set.mk)
end core
