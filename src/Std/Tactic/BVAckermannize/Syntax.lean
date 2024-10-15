/-
Copyright (c) 2024 Siddharth Bhat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat
-/
prelude
import Init.Notation
import Init.Simproc

set_option linter.missingDocs true -- keep it documented

namespace Lean.Parser

namespace Tactic

/--
Close fixed-width `BitVec`, `Bool`, and uninterpreted function goals by obtaining a proof from an external SAT solver and
verifying it inside Lean. The solvable goals are currently limited to the Lean equivalent of
[`QF_BV`](https://smt-lib.org/logics-all.shtml#QF_BV) + [`QF_UF`](https://smt-lib.org/logics-all.shtml#QF_UF)

```lean
example : ∀ (a b : BitVec 64), (a &&& b) + (a ^^^ b) = a ||| b := by
  intros
  bv_decide
```
-/
syntax (name := bvAckEager) "bv_ack_eager" : tactic

end Tactic

end Lean.Parser
