/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module

prelude
public import Init.Notation

public section

namespace Lean.Order
/--
`monotonicity` performs one compositional step solving `monotone` goals,
using lemma tagged with `@[partial_fixpoint_monotone]`.

This tactic is mostly used internally by lean in `partial_fixpoint` definitions, but
can be useful on its own for debugging or when proving new `@[partial_fixpoint_monotone]` lemmas.
-/
scoped syntax (name := monotonicity) "monotonicity" : tactic

end Lean.Order
