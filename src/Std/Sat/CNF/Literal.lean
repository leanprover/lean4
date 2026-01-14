/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
module

prelude
public import Init.Data.Hashable
public import Init.Data.ToString

@[expose] public section

namespace Std
namespace Sat

/--
CNF literals identified by some type `α`. The `Bool` is the polarity of the literal.
`true` means positive polarity.
-/
abbrev Literal (α : Type u) := α × Bool

namespace Literal

/--
Flip the polarity of `l`.
-/
@[inline, grind =]
def negate (l : Literal α) : Literal α := (l.1, !l.2)

end Literal

end Sat
end Std
