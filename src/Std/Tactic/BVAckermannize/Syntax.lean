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
This tactic performs eager ackermannization, which is an algorithmic technique to convert QF_UF_BV into QF_BV.

On every function application of the form `(f x1 x2 ... xn)`
where the type signature of `f` is `BitVec k1 -> BitVec k2 -> ... -> BitVec kn -> BitVec ko`,
it creates a new variable `fAppX : BitVec k0`, and an equation `fAppX = f x1 ... xn`.
Next, when it encounters another application of the same function `(f y1 y2 ... yn)`,
it creates a new variable `fAppY : BitVec k0`, and another equation `fAppY = f y1 ... yn`,
along with another equation (the congruence lemma), which states:

```
hAppXAppYExt: x1 = x2 -> y1 = y2 -> ... xn = yn -> fAppX = fAppY
```

Intuitively, this is the only fact that they theory UF can propagate,
and we thus encode it directly as a SAT formula,
by abstracting out the actual function application into a new free variable.

For a given function symbol `f`, if there are `n` applications of `f`,
we create `O(n²)` congruence lemmas to propagate information about all pairs of
applications.

```lean
example : ∀ (m : BitVec 64) (P : BitVec 64 → Bool)
    (h : m ≤ 0x00000006 ∧
         P 0x00000000 ∧
         P 0x00000001 ∧
         P 0x00000002 ∧
         P 0x00000003 ∧
         P 0x00000004 ∧
         P 0x00000005 ∧
         P 0x00000006),
    P m := by
  bv_ack_eager -- reduce to BV problem.
  bv_decide
```
-/
syntax (name := bvAckEager) "bv_ack_eager" : tactic

end Tactic

end Lean.Parser
