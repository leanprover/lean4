/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: init.default
Authors: Leonardo de Moura, Jakob von Raumer
-/

prelude
import init.datatypes init.reserved_notation init.tactic init.logic
import init.bool init.num init.priority init.relation init.wf
import init.types
import init.trunc init.path init.equiv init.util
import init.ua init.funext
import init.hedberg init.nat init.hit

namespace core
  export bool empty unit sum sigma
  export [notations] prod
  export eq (idp idpath concat inverse transport ap ap10 cast tr_inv homotopy ap11 apd)
  export [declarations] function
  export equiv (to_inv to_right_inv to_left_inv)
  export is_equiv (inv right_inv left_inv)

end core
