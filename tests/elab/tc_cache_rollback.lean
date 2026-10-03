import Lean

/-!
Rolling back an environment change through `SavedState.restore` drops the type class resolution
cache entries recorded after it, as a different change could later bring the recorded generations or
declaration change log position back, or reuse the name of a removed constant, and keeps the entries
recorded before the rollback point. The latest recording start is carried over the rollback, so that
changes the surviving entries depend on stay logged.
-/

open Lean Meta Elab Command

class Foo where
  val : Nat

@[instance_reducible] def a : Foo := ⟨1⟩
@[instance_reducible] def b : Foo := ⟨2⟩

/-- info: a then b -/
#guard_msgs in
run_meta do
  let s ← saveState
  liftCommandElabM <| elabCommand (← `(attribute [instance] a))
  let r₁ ← synthInstance (mkConst ``Foo)
  s.restore
  liftCommandElabM <| elabCommand (← `(attribute [instance] b))
  let r₂ ← synthInstance (mkConst ``Foo)
  logInfo m!"{r₁} then {r₂}"

class Bar where

instance : Bar := ⟨⟩

class Baz where

/--
trace: [Meta.synthInstance.cache] new: Bar
[Meta.synthInstance.cache] cached: Bar
-/
#guard_msgs in
run_meta do
  let cmd ← `(instance : Baz := ⟨⟩)
  withOptions (·.setBool `trace.Meta.synthInstance.cache true) do
    discard <| synthInstance (mkConst ``Bar)
    let s ← saveState
    liftCommandElabM <| elabCommand cmd
    s.restore
    discard <| synthInstance (mkConst ``Bar)

class Q (α : Type) where

instance : Q Nat := ⟨⟩

def X := Nat
def Y := Nat

-- A logged reducibility change rolled back and replaced by another logged change at the same
-- position of the declaration change log: the entry recorded in between must not be served.
/-- info: false then true then false -/
#guard_msgs in
run_meta do
  let before := (← synthInstance? (mkApp (mkConst ``Q) (mkConst ``X))).isSome
  let s ← saveState
  liftCommandElabM <| elabCommand (← `(attribute [reducible] X))
  let during := (← synthInstance? (mkApp (mkConst ``Q) (mkConst ``X))).isSome
  s.restore
  liftCommandElabM <| elabCommand (← `(attribute [reducible] Y))
  let after := (← synthInstance? (mkApp (mkConst ``Q) (mkConst ``X))).isSome
  logInfo m!"{before} then {during} then {after}"

class Q' (α : Type) where

instance : Q' Nat := ⟨⟩

-- `D` is added after the latest recording start, and the query observing it runs after the save
-- point. Restoring must not roll the recording start back past `D`, as `D`'s later reducibility
-- change would then go unlogged while the entry survives.
/-- info: false then true -/
#guard_msgs in
run_meta do
  addDecl <| .defnDecl {
    name := `D, levelParams := [], type := mkSort 1, value := mkConst ``Nat,
    hints := .regular 0, safety := .safe }
  let q := mkApp (mkConst ``Q') (mkConst `D)
  let s ← saveState
  let during := (← synthInstance? q).isSome
  s.restore
  (Attribute.add `D `reducible .missing : CoreM Unit)
  let after := (← synthInstance? q).isSome
  logInfo m!"{during} then {after}"

-- A constant added after the save point is observed and then removed by the restore; a constant of
-- the same name added after another one gets a later generation than the entry's recording start,
-- so the entry must not survive the rollback.
/-- info: false then true -/
#guard_msgs in
run_meta do
  let mkDef (n : Name) : Declaration := .defnDecl {
    name := n, levelParams := [], type := mkSort 1, value := mkConst ``Nat,
    hints := .regular 0, safety := .safe }
  let q := mkApp (mkConst ``Q') (mkConst `E)
  let s ← saveState
  addDecl (mkDef `E)
  let during := (← synthInstance? q).isSome
  s.restore
  addDecl (mkDef `F)
  addDecl (mkDef `E)
  (Attribute.add `E `reducible .missing : CoreM Unit)
  let after := (← synthInstance? q).isSome
  logInfo m!"{during} then {after}"

-- `Term.observing` followed by `applyResult` rolls back a constant and restores it again: the
-- entries recorded after the constant must be served again rather than recomputed.
/--
trace: [Meta.synthInstance.cache] new: Q' Nat
[Meta.synthInstance.cache] cached: Q' Nat
-/
#guard_msgs in
run_meta do
  let s0 ← saveState
  addDecl <| .defnDecl {
    name := `G, levelParams := [], type := mkSort 1, value := mkConst ``Nat,
    hints := .regular 0, safety := .safe }
  let q := mkApp (mkConst ``Q') (mkConst ``Nat)
  withOptions (·.setBool `trace.Meta.synthInstance.cache true) do
    discard <| synthInstance? q
  let s1 ← saveState
  s0.restore
  s1.restore
  withOptions (·.setBool `trace.Meta.synthInstance.cache true) do
    discard <| synthInstance? q
