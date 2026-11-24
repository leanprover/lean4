import Lean

/-!
Regression test for #16675 (and the related #15100, #15101): `Kernel.Environment.replay` must
reject a map entry whose key differs from the name of the constant stored under it. Otherwise a
recursor, constructor or quotient entry stored under a fresh key is never compared against the
kernel-generated declaration.
-/

open Lean

inductive T where
  | mk

def replayWith (extra : Option (Name × ConstantInfo)) : MetaM Unit := do
  let env ← getEnv
  let mut consts : Std.HashMap Name ConstantInfo :=
    env.constants.map₂.foldl (init := ∅) fun consts n info => consts.insert n info
  if let some (n, ci) := extra then
    consts := consts.insert n ci
  let some importEnv := env.importEnv?
    | unreachable!
  discard <| importEnv.toKernelEnv.replay consts

-- The unmodified environment replays fine.
run_meta replayWith none

/-- error: declaration 'T.rec' is stored under the name 'renamed' -/
#guard_msgs in
run_meta show MetaM Unit from do
  let .recInfo rv ← getConstInfo ``T.rec | unreachable!
  replayWith (some (`renamed, .recInfo { rv with levelParams := [], type := .const ``False [] }))

/-- error: declaration 'T.mk' is stored under the name 'renamed' -/
#guard_msgs in
run_meta show MetaM Unit from do
  let .ctorInfo cv ← getConstInfo ``T.mk | unreachable!
  replayWith (some (`renamed, .ctorInfo { cv with type := .const ``False [] }))

/-- error: declaration 'Quot.lift' is stored under the name 'renamed' -/
#guard_msgs in
run_meta show MetaM Unit from do
  let .quotInfo qv ← getConstInfo ``Quot.lift | unreachable!
  replayWith (some (`renamed, .quotInfo { qv with levelParams := [], type := .const ``False [] }))
