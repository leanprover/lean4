import Lean

/-!
Tests that type class resolution cache entries whose query mentions a free variable are not
persisted across commands.

A `FVarId` identifies a variable only relative to the `NameGenerator` that created it, and code may
restart one (e.g. `grind`'s theorem instantiation does), after which the same `FVarId` denotes a
different variable. Here two commands create the same `FVarId`, first for a variable and then for a
`let` variable with a value, so that the query fails in the first command and succeeds in the
second.
-/

open Lean Meta

class Foo (α : Type) where

instance : Foo Nat := ⟨⟩

/-- Runs `x` with a name generator that creates the same ids in every command. -/
def withRestartedNGen (x : MetaM α) : MetaM α := do
  let ngen ← getNGen
  try
    setNGen { namePrefix := `_tc_cache_test }
    x
  finally
    setNGen ngen

def query (α : Expr) : MetaM Unit := do
  let r? ← withOptions (·.setBool `trace.Meta.synthInstance.cache true) do
    synthInstance? (mkApp (mkConst ``Foo) α)
  logInfo m!"{α.fvarId!.name}: {r?.isSome}"

/--
info: _tc_cache_test.1: false
---
trace: [Meta.synthInstance.cache] new: Foo α
-/
#guard_msgs in
run_meta withRestartedNGen do
  withLocalDeclD `α (mkSort 1) query

-- The same `FVarId` now is a `let` variable with value `Nat`, so the failure above must not be
-- reused.
/--
info: _tc_cache_test.1: true
---
trace: [Meta.synthInstance.cache] new: Foo α
-/
#guard_msgs in
run_meta withRestartedNGen do
  withLetDecl `α (mkSort 1) (mkConst ``Nat) query
