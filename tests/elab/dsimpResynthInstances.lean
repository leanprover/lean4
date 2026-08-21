module

/-!
Tests for `dsimp.resynthInstances`: after a definitional rewrite of an argument, `simp` and
`dsimp` check the instance arguments whose types depend on it at `.instances` transparency.
A resynthesized instance is adopted when it is defeq to the old one at `.implicit`
transparency; otherwise the rewrite of the argument is refused.
-/

class X (n : Nat)

@[implicit_reducible]
def natZero := 0

instance instXNatZero : X natZero where

theorem natZero_def : natZero = 0 := rfl

def g (m : Nat) [X m] : Nat := m + 1

theorem g_eq {m} [X m] : g m = m + 1 := by
  simp [g]

/-!
Refusal: there is no `X 0` instance, so the rewrite `natZero ↦ 0` inside `g` is refused with a
warning. `g_eq` then still applies, and the goal closes.
-/

/--
warning: A rewrite with natZero_def changed an argument of
  g natZero
The instance argument
  instXNatZero
then does not have the expected type at `.instances` transparency, and no usable replacement instance was found. The rewrite was not applied here.

Note: Disable this warning with `set_option dsimp.resynthInstances.warning false`, or the whole check with `set_option dsimp.resynthInstances false`.
-/
#guard_msgs in
example : g natZero = 1 := by
  simp only [natZero_def, g_eq]

/-!
Adoption: `Y` has instances for both `natZeroY` and `0`, and they are defeq at `.implicit`
transparency. The rewrite goes through with the resynthesized instance, silently (the trace
shows the adoption).
-/

class Y (n : Nat)

@[implicit_reducible]
def natZeroY := 0

instance instYNatZeroY : Y natZeroY where
instance instY0 : Y 0 where

theorem natZeroY_def : natZeroY = 0 := rfl

def gY (m : Nat) [Y m] : Nat := m + 1

theorem gY_eq {m} [Y m] : gY m = m + 1 := by
  simp [gY]

/--
trace: [Meta.Tactic.simp.resynthInstances] adopted resynthesized instance in
      gY natZeroY
    old instance
      instYNatZeroY
    new instance
      instY0
-/
#guard_msgs in
set_option trace.Meta.Tactic.simp.resynthInstances true in
example : gY natZeroY = 1 := by
  simp only [natZeroY_def, gY_eq]

/-!
Standalone `dsimp` refuses the rewrite inside `g` but performs it elsewhere.
-/

/--
warning: A rewrite with natZero_def changed an argument of
  g natZero
The instance argument
  instXNatZero
then does not have the expected type at `.instances` transparency, and no usable replacement instance was found. The rewrite was not applied here.

Note: Disable this warning with `set_option dsimp.resynthInstances.warning false`, or the whole check with `set_option dsimp.resynthInstances false`.
-/
#guard_msgs in
example : g natZero = natZero + 1 := by
  dsimp only [natZero_def]
  exact g_eq

/-!
`dsimp.resynthInstances.warning := false` silences the warning; the refusal still happens.
-/

#guard_msgs in
set_option dsimp.resynthInstances.warning false in
example : g natZero = 1 := by
  simp only [natZero_def, g_eq]

/-!
A class marked `@[lax_instance_defeq]` is exempt: the rewrite goes through unchecked as in the
old behavior, producing the stale term `@gZ 0 instZNatZeroZ`. Since the class is also exempt
from the strict assignment check in `isDefEq`, `gZ_eq` still applies (the instance assignment
is checked at `.implicit`, where `natZeroZ` unfolds), and the goal closes silently.
-/

@[lax_instance_defeq]
class Z (n : Nat)

@[implicit_reducible]
def natZeroZ := 0

instance instZNatZeroZ : Z natZeroZ where

theorem natZeroZ_def : natZeroZ = 0 := rfl

def gZ (m : Nat) [Z m] : Nat := m + 1

theorem gZ_eq {m} [Z m] : gZ m = m + 1 := by
  simp [gZ]

#guard_msgs in
example : gZ natZeroZ = 1 := by
  simp only [natZeroZ_def, gZ_eq]

/-!
The attribute can be applied retroactively and locally; outside the section, `X` is strict
again.
-/

section
attribute [local lax_instance_defeq] X

#guard_msgs in
example : g natZero = 1 := by
  simp only [natZero_def, g_eq]

end

/--
warning: A rewrite with natZero_def changed an argument of
  g natZero
The instance argument
  instXNatZero
then does not have the expected type at `.instances` transparency, and no usable replacement instance was found. The rewrite was not applied here.

Note: Disable this warning with `set_option dsimp.resynthInstances.warning false`, or the whole check with `set_option dsimp.resynthInstances false`.
-/
#guard_msgs in
example : g natZero = 1 := by
  simp only [natZero_def, g_eq]

/-!
Only classes can be marked.
-/

/--
error: invalid `lax_instance_defeq`, `Nat.add` is not a class
-/
#guard_msgs in
attribute [lax_instance_defeq] Nat.add

/-!
Propositional classes are exempt by default, without the attribute; same behavior as above.
-/

class P (n : Nat) : Prop

@[implicit_reducible]
def natZeroP := 0

instance instPNatZeroP : P natZeroP where

theorem natZeroP_def : natZeroP = 0 := rfl

def gP (m : Nat) [P m] : Nat := m + 1

theorem gP_eq {m} [P m] : gP m = m + 1 := by
  simp [gP]

#guard_msgs in
example : gP natZeroP = 1 := by
  simp only [natZeroP_def, gP_eq]

/-!
`dsimp.resynthInstances := false` restores the old behavior: the stale term `@g 0 instXNatZero`
is produced, `g_eq` no longer applies, and the goal remains open.
-/

/--
error: unsolved goals
⊢ g 0 = 1
-/
#guard_msgs in
set_option dsimp.resynthInstances false in
example : g natZero = 1 := by
  simp only [natZero_def, g_eq]
