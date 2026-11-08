/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Init.Util

/-!
# InLean: `withExclusive`, the reference-count read behind the walk memos

Twin of con-leche's `ConLeche.Kernel.Exclusive`, to be replaced by the
standard library's `withExclusive` (`Init.Util`) when the toolchain carries
it; the two definitions below are written to that interface.

`withExclusive a k h` runs `k` on whether the object `a` is *exclusive* —
single-threaded with reference count exactly 1, so that no other reference
to it exists.  In the logic it is `k false` ("not known to be exclusive");
in compiled code `@[implemented_by]` substitutes `k (isExclusiveUnsafe a)`,
the count read off the object header (`lean_is_exclusive_obj`, a BORROWED
parameter).  A multi-threaded object and a persistent one answer `false`,
the safe side.

**What justifies the substitution** is the obligation `h : k true = k false`:
the continuation's value does not depend on the answer, so the compiled
program computes the value the definition names.  A caller may use the
answer to choose *how* to compute a value, never *which* value — the
arrangement of `Init.Util`'s `withPtrAddr`.

**What it is for.**  A walk's memo exists so that a node reached twice — a
shared sub-DAG — is visited once.  A node with exactly one reference cannot
be reached twice, so recording it is pure loss; the official kernel's
`replace_fn` caches a node only when `!is_likely_unshared(e)`, the same read.
The walks (`Lean.Kernel.InLean.ExprOps`) and the equalities (`Lean.Kernel.InLean.ExprEq`) return a
`Squash` (a subsingleton), so `h` is `Subsingleton.elim` (`withExcl`).

**The borrowed-parameter requirement.**  An owned parameter, a `let` keeping
the object alive across the call, a closure capturing it or a `Prod` holding
it is a second reference, and the read then answers `false` for every node.
This module is `@[inline]` down to the `@[extern]` call, and the walks pass
their node borrowed (`@&`), so the count read is the count of references
inside the term.

**Trust.**  The one `unsafe`-implemented primitive of InLean: the trust
surface gate allowlists this file for `unsafe` and `implemented_by`, with
this docstring as the justification.  Nothing is taken on faith beyond what
`withPtrAddr` already asks — that `lean_is_exclusive_obj` returns a `Bool`
and has no other effect; *which* `Bool` is irrelevant to every theorem, by
`h`.
-/

@[expose] public section

namespace Lean.Kernel.InLean

set_option linter.unusedVariables.funArgs false in
/-- The compiled `withExclusive`: the continuation on the object's real
exclusivity.  Inlined into its caller, so the object reaches the
`@[extern]` check as the caller's own variable, borrowed by the check's
signature. -/
@[inline] unsafe def withExclusiveUnsafe {α : Type u} {β : Type v} (a : α)
    (k : Bool → β) (h : k true = k false) : β :=
  k (isExclusiveUnsafe a)

/-- Run `k` on whether `a` is an exclusive object (reference count 1) in
compiled code; in the logic, on `false`.  The obligation says the
continuation's value does not depend on the answer. -/
@[implemented_by withExclusiveUnsafe]
def withExclusive {α : Type u} {β : Type v} (a : α) (k : Bool → β)
    (h : k true = k false) : β :=
  k false

/-- `withExclusive` into a subsingleton: the obligation is
`Subsingleton.elim`. -/
@[inline] def withExcl {α : Type u} {β : Type v} [Subsingleton β] (a : α)
    (k : Bool → β) : β :=
  withExclusive a k (Subsingleton.elim _ _)

end Lean.Kernel.InLean
