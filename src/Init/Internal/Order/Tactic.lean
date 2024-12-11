/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude
import Init.Notation

namespace Lean.Order

/--
`monotonicity` performs one compositional step solving `monotone` goals,
using lemma tagged with `@[partial_monotone]`.

This tactic is mostly used internally by lean in `partial_fixpoint` definitions, but
can be useful on its own for debugging or when proving new `@[partial_monotone]` lemmas.
-/
scoped syntax (name := monotonicity) "monotonicity" : tactic

/--
Registers a monotonicity lemma, to be used when constructing recursive functions using
`partial_fixpoint`.

This attribute is scoped in the `Lean.Order` namespace.
-/
scoped macro "monotone" : attr => `(attr|internal_monotone)

end Lean.Order
