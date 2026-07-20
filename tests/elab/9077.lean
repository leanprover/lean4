/-!
Regression test for #9077: instance synthesis must not commit to an instance for a type
that is different at instance-resolution time (e.g. across a semireducible type synonym),
which used to happen when unification assigned an instance metavariable a value of the
wrong type.

Tests the modes of `backward.isDefEq.instanceTypes`:
- `"none"`: no restriction (the buggy pre-#9077-fix behavior),
- `"mark"`: reject wrong-typed assignments, propagate the restriction to spine mvars,
- `"synth"`/`"markOrSynth"`: reject, but fall back to synthesizing the instance and
  unifying the candidate value with the result.
-/

class P (α : Type) where p : Nat
class Q (α : Type) extends P α where
structure H (α : Type) {p : P α} [p' : P α] (h : p = p') where
class N (β : Type) where
instance inst (α : Type) [q : Q α] : N (H α (p := q.toP) rfl) where

def Copy (α : Type) := α

set_option backward.isDefEq.respectTransparency false

instance pCopy [P E] : P (Copy E) := (inferInstance : P E)

/-!
Scenario 1 (the original repro shape): `inst : N (H (Copy E) rfl)` needs `Q (Copy E)`, but
we only have `iQ : Q E`, and these types are not instance-reducibly equal. In `"none"` mode,
after `synthPending` fails to synthesize `?q : Q (Copy E)`, unification assigns it anyway:
`pCopy (inst := iQ.toP) =?= ?q.toP` unfolds `pCopy`, giving `iQ.toP =?= ?q.toP` and finally
`(?q : Q (Copy E)) := (iQ : Q E)`. All other modes reject this assignment, and since no
`Q (Copy E)` instance exists, the synthesis fallback of `"synth"`/`"markOrSynth"` fails too.
-/

/-- info: inst (Copy E) -/
#guard_msgs in
set_option backward.isDefEq.instanceTypes "none" in
variable (E : Type) [iQ : Q E] in
#synth N (H (Copy E) rfl)

/--
error: failed to synthesize
  N (H (Copy E) ⋯)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option backward.isDefEq.instanceTypes "mark" in
variable (E : Type) [iQ : Q E] in
#synth N (H (Copy E) rfl)

/--
error: failed to synthesize
  N (H (Copy E) ⋯)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option backward.isDefEq.instanceTypes "synth" in
variable (E : Type) [iQ : Q E] in
#synth N (H (Copy E) rfl)

/--
error: failed to synthesize
  N (H (Copy E) ⋯)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option backward.isDefEq.instanceTypes "markOrSynth" in
variable (E : Type) [iQ : Q E] in
#synth N (H (Copy E) rfl)

/-!
Scenario 2: unification directly proposes `(?q : Q (Copy E)) := (iQ : Q E)` because the
instance value occurs in the goal type. Without a `Q (Copy E)` instance, `"none"` exhibits
the bug and the other modes fail.
-/

structure G (α : Type) (q : Q α) where
class M (β : Type) where
instance instG (α : Type) [q : Q α] : M (G α q) where

/-- info: instG (Copy E) -/
#guard_msgs in
set_option backward.isDefEq.instanceTypes "none" in
variable (E : Type) [iQ : Q E] in
#synth M (G (Copy E) iQ)

/--
error: failed to synthesize
  M (G (Copy E) iQ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option backward.isDefEq.instanceTypes "mark" in
variable (E : Type) [iQ : Q E] in
#synth M (G (Copy E) iQ)

/--
error: failed to synthesize
  M (G (Copy E) iQ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option backward.isDefEq.instanceTypes "synth" in
variable (E : Type) [iQ : Q E] in
#synth M (G (Copy E) iQ)

/--
error: failed to synthesize
  M (G (Copy E) iQ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option backward.isDefEq.instanceTypes "markOrSynth" in
variable (E : Type) [iQ : Q E] in
#synth M (G (Copy E) iQ)

/-!
Scenario 3: like scenario 2, but the correct instance `qCopy : Q (Copy E)` exists and is
definitionally equal to the rejected candidate `iQ`. `"mark"` still fails — this is the
brittleness the synthesis fallback addresses — while `"synth"` and `"markOrSynth"`
synthesize `qCopy`, unify it with the candidate, and succeed.
-/

instance qCopy [Q E] : Q (Copy E) := ‹Q E›

/-- info: instG (Copy E) -/
#guard_msgs in
set_option backward.isDefEq.instanceTypes "none" in
variable (E : Type) [iQ : Q E] in
#synth M (G (Copy E) iQ)

/--
error: failed to synthesize
  M (G (Copy E) iQ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option backward.isDefEq.instanceTypes "mark" in
variable (E : Type) [iQ : Q E] in
#synth M (G (Copy E) iQ)

/-- info: instG (Copy E) -/
#guard_msgs in
set_option backward.isDefEq.instanceTypes "synth" in
variable (E : Type) [iQ : Q E] in
#synth M (G (Copy E) iQ)

/-- info: instG (Copy E) -/
#guard_msgs in
set_option backward.isDefEq.instanceTypes "markOrSynth" in
variable (E : Type) [iQ : Q E] in
#synth M (G (Copy E) iQ)

/-! An invalid option value is reported when the check is first consulted. -/

/--
error: invalid value `bogus` for option `backward.isDefEq.instanceTypes`, valid values are "none", "mark", "synth", and "markOrSynth"
-/
#guard_msgs in
set_option backward.isDefEq.instanceTypes "bogus" in
variable (E : Type) [iQ : Q E] in
#synth M (G (Copy E) iQ)
