/-! Tests that type class resolution does not supply an instance argument for the wrong expected
type via unification (the default `tcUnifyInstanceImplicits false` behavior). See issue #9077. -/

class P (α : Type) where p : Nat
class Q (α : Type) extends P α where
structure H (α : Type) {p : P α} [p' : P α] (h : p = p') where
class N (β : Type) where
instance inst (α : Type) [q : Q α] : N (H α (p := q.toP) rfl) where

def Copy (α : Type) := α

set_option backward.isDefEq.respectTransparency false

instance pCopy [P E] : P (Copy E) := (inferInstance : P E)

/-
On an earlier version, this synthetization worked unintentionally:
`inst : N (H (Copy E) rfl)` needs `Q (Copy E)`, but we only have `iQ : Q E`, and these types are not instance-reducibly equal.

However, after instance resolution (`synthPending`) fails to synthesize `?q : Q (Copy E)`,
we syntesize it by unification:
`pCopy (inst := iQ.toP) =?= ?q.toP` (unfolding `pCopy` because it's implicit-reducible and we bumped transparency for `H`'s implicit argument `p`.)
`iQ.toP =?= ?q.toP`
`iQ =?= ?q` (types match at implicit transparency)

So we assign `(?q : Q (Copy E)) := (iQ : Q E)`.
-/

/--
error: failed to synthesize
  N (H (Copy E) ⋯)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
variable (E : Type) [iQ : Q E] in
#synth N (H (Copy E) rfl)
