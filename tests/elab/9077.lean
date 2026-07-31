/-!
Regression test for #9077: instance synthesis must not commit to an instance for a type
that is different at instance-resolution time (e.g. across a semireducible type synonym),
which used to happen when unification assigned an instance metavariable a value of the
wrong type.

Tests both settings of `backward.isDefEq.instanceTypes`:
- `false`: no restriction (the buggy pre-#9077-fix behavior),
- `true`: reject wrong-typed assignments, falling back to synthesizing the instance and
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
we only have `iQ : Q E`, and these types are not instance-reducibly equal. With `false`,
after `synthPending` fails to synthesize `?q : Q (Copy E)`, unification assigns it anyway:
`pCopy (inst := iQ.toP) =?= ?q.toP` unfolds `pCopy`, giving `iQ.toP =?= ?q.toP` and finally
`(?q : Q (Copy E)) := (iQ : Q E)`. With `true` this assignment is rejected, and since no
`Q (Copy E)` instance exists, the synthesis fallback fails too.
-/

/-- info: inst (Copy E) -/
#guard_msgs in
set_option backward.isDefEq.instanceTypes false in
variable (E : Type) [iQ : Q E] in
#synth N (H (Copy E) rfl)

/--
error: failed to synthesize
  N (H (Copy E) ⋯)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option backward.isDefEq.instanceTypes true in
variable (E : Type) [iQ : Q E] in
#synth N (H (Copy E) rfl)

/-!
Scenario 2: unification directly proposes `(?q : Q (Copy E)) := (iQ : Q E)` because the
instance value occurs in the goal type. Without a `Q (Copy E)` instance, `false` exhibits
the bug and `true` fails.
-/

structure G (α : Type) (q : Q α) where
class M (β : Type) where
instance instG (α : Type) [q : Q α] : M (G α q) where

/-- info: instG (Copy E) -/
#guard_msgs in
set_option backward.isDefEq.instanceTypes false in
variable (E : Type) [iQ : Q E] in
#synth M (G (Copy E) iQ)

/--
error: failed to synthesize
  M (G (Copy E) iQ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option backward.isDefEq.instanceTypes true in
variable (E : Type) [iQ : Q E] in
#synth M (G (Copy E) iQ)

/-!
Scenario 3: like scenario 2, but the correct instance `qCopy : Q (Copy E)` exists and is
definitionally equal to the rejected candidate `iQ`. Merely rejecting the assignment would
fail here — this is the brittleness the synthesis fallback addresses: `true` synthesizes
`qCopy`, unifies it with the candidate, and succeeds.
-/

instance qCopy [Q E] : Q (Copy E) := ‹Q E›

/-- info: instG (Copy E) -/
#guard_msgs in
set_option backward.isDefEq.instanceTypes false in
variable (E : Type) [iQ : Q E] in
#synth M (G (Copy E) iQ)

/-- info: instG (Copy E) -/
#guard_msgs in
set_option backward.isDefEq.instanceTypes true in
variable (E : Type) [iQ : Q E] in
#synth M (G (Copy E) iQ)

/-!
Scenario 4 (minimized from `let x : Std.HashSet _ := ∅` in Mathlib): the goal type contains
the *caller's* pending instance metavariables (created for the instance-implicit arguments
of `Box` while its type argument is still undetermined), and unification assigns them to the
search's subgoal metavariables. These caller metavariables are not assignable during the
search, so `true` accepts them in the spine rather than demanding an mvar-free value it
could not synthesize; the elaborator synthesizes them later, once `useBox x` determines the
type argument.
-/

class R (α : Type) where
structure Box (α : Type) [R α] where mk' ::
class Init (γ : Type) where init : γ
instance instR : R Nat := ⟨⟩
instance instInitBox (α : Type) [R α] : Init (Box α) := ⟨⟨⟩⟩

def useBox (_b : Box Nat) : Nat := 0

#guard_msgs in
set_option backward.isDefEq.instanceTypes false in
example : Nat :=
  let x : Box _ := Init.init
  useBox x

#guard_msgs in
set_option backward.isDefEq.instanceTypes true in
example : Nat :=
  let x : Box _ := Init.init
  useBox x
