/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
prelude
import Init.Data.Hashable
import Init.Data.ToString
import Std.Sat.Basic

namespace Std
namespace Sat

/--
CNF literals identified by some type `α`. The `Bool` is the polarity of the literal.
`true` means positive polarity.
-/
abbrev Literal (α : Type u) := α × Bool

namespace Literal
variable (α : Type) [Hashable α]

instance : HSat α (Literal α) where
  eval := fun p l => p l.1 = l.2

instance (p : α → Bool) (l : Literal α) : Decidable (p ⊨ l) :=
  inferInstanceAs (Decidable (p l.1 = l.2))

/--
Flip the polarity of `l`.
-/
def negate (l : Literal α) : Literal α := (l.1, not l.2)

/--
Output `l` as a DIMACS literal identifier.
-/
def dimacs [ToString α] (l : Literal α) : String :=
  if l.2 then
    s!"{l.1}"
  else
    s!"-{l.1}"

end Literal

end Sat
end Std
