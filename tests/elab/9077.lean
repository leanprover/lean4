/-!
Regression test for #9077: instance synthesis must not synthesize instances whose type doesn't match
the expected type at instance transparency. Notable exception: outParams might only unify at a
higher transparency.

Tests both settings of `backward.isDefEq.respectTransparency.instanceSearchTypes`:
- `false`: old behavior,
- `true`: reject assignments to instance-implicit argument metavariables of the wrong type, falling
  back to synthesizing the instance and unifying the candidate value with the result.
-/

class P (α : Type) where p : Nat
class Q (α : Type) extends P α where
structure H (α : Type) {p : P α} [p' : P α] (h : p = p') where
class N (β : Type) where
instance inst (α : Type) [q : Q α] : N (H α (p := q.toP) rfl) where

@[implicit_reducible]
def Copy (α : Type) := α

instance pCopy [P E] : P (Copy E) := (inferInstance : P E)

/-!
Scenario 1, minimization of #9077's reproducer: `inst : N (H (Copy E) rfl)` requires a `Q (Copy E)`
instance, but we only have `iQ : Q E`. Therefore, instance synthesis should fail.
With `false`, the instance is assigned by unification anyway: It sees the problem
`pCopy (inst := iQ.toP) =?= ?q.toP`, unfolds `pCopy`, obtains `iQ.toP =?= ?q.toP` and finally
assigns `(?q : Q (Copy E)) := (iQ : Q E)`.
With `true`, this assignment is rightfully rejected.
-/

/-- info: inst (Copy E) -/
#guard_msgs in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
variable (E : Type) [iQ : Q E] in
#synth N (H (Copy E) rfl)

/--
error: failed to synthesize
  N (H (Copy E) ⋯)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes true in
variable (E : Type) [iQ : Q E] in
#synth N (H (Copy E) rfl)

/-!
Scenario 2: unification assigns `(?q : Q (Copy E)) := (iQ : Q E)`.
Without a `Q (Copy E)` instance, `false` exhibits
the bug and `true` fails. The latter is expected.
-/

structure G (α : Type) (q : Q α) where
class M (β : Type) where
instance instG (α : Type) [q : Q α] : M (G α q) where

/-- info: instG (Copy E) -/
#guard_msgs in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
variable (E : Type) [iQ : Q E] in
#synth M (G (Copy E) iQ)

/--
error: failed to synthesize
  M (G (Copy E) iQ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes true in
variable (E : Type) [iQ : Q E] in
#synth M (G (Copy E) iQ)

/-!
Scenario 3: like scenario 2, but the correct instance `qCopy : Q (Copy E)` exists and is
definitionally equal to the rejected candidate `iQ`. It would be brittle to simply reject the
assignment in this case. Instead, we synthesize the "correct" instance and then check that it
unifies with the wrongly typed one, at ambient transparency, usually implicit.
-/

instance qCopy [Q E] : Q (Copy E) := ‹Q E›

/-- info: instG (Copy E) -/
#guard_msgs in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
variable (E : Type) [iQ : Q E] in
#synth M (G (Copy E) iQ)

/-- info: instG (Copy E) -/
#guard_msgs in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes true in
variable (E : Type) [iQ : Q E] in
#synth M (G (Copy E) iQ)

/-!
Regression test for a failure observed after introducing the new behavior, minimized from
`let x : Std.HashSet _ := ∅` occurrences. The instance's expected type contains an unassigned
metavariable, which is unassignable during instance search. This metavariable does not originate
from an instance-implicit argument. Still, we allow this metavariable in spine positions of the
assignment.
-/

class R (α : Type) where
structure Box (α : Type) [R α] where mk' ::
class Init (γ : Type) where init : γ
instance instR : R Nat := ⟨⟩
instance instInitBox (α : Type) [R α] : Init (Box α) := ⟨⟨⟩⟩

def useBox (_b : Box Nat) : Nat := 0

#guard_msgs in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
example : Nat :=
  let x : Box _ := Init.init
  useBox x

#guard_msgs in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes true in
example : Nat :=
  let x : Box _ := Init.init
  useBox x
