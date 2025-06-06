prelude
import Std.Data.Ranges.Basic
import Std.Data.Ranges.Slice

-- Have: `LE`, `LT`, `HAdd`
-- Perhaps need: `Succ`
-- In general, how can we avoid cases like the zero step size?

/-
* run a tactic when the range is built up
  * check the "validity" of the step size or
  * try to prove finiteness, and if possible, attach a finiteness hint

The former is weird because "validity" isn't always equivalent to "finiteness".
Its meaning could depend on the bound shape.
For certain types, not just the bound shape is relevant, but also the concrete
bounds; for example, take `Option Int`, with `none` being the smallest element.

The latter requires metaprogramming work and will silently fail.

Both increase the dependentness of the code.
Idea for extrinsic termination proofs:
* Assume that the partial and the well-founded implementations are equivalent.
* Use `implemented_by` to use either definition as the kernel definition,
  but always the partial one as the implementation.
* Can prove things about `toList`, `forIn` etc. if and only if finiteness can
  be proved.

HACK: have a very low-prioritized non-terminating `ForIn` instance.
-/
