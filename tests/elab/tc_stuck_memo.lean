import Lean

/-!
Tests the memoization of type class resolution queries that get stuck on a metavariable. The
elaborator retries such a query whenever it makes progress; a retry fails fast as long as nothing
the stuckness depends on has changed.
-/

open Lean Meta

class Foo (α : Type) where
class Baz (α : Type) where
instance : Foo Nat := ⟨⟩
instance : Foo Int := ⟨⟩
instance [Foo Int] : Baz Int := ⟨⟩
instance : Baz Nat := ⟨⟩

def synth (type : Expr) : MetaM Unit :=
  withOptions (·.setBool `trace.Meta.synthInstance.cache true) do
    match ← trySynthInstance type with
    | .some inst => logInfo m!"{inst}"
    | .none      => logInfo "none"
    | .undef     => logInfo "stuck"

-- A retry of a stuck query is not searched again. Assigning the metavariable changes the query.
/--
info: stuck
---
info: stuck
---
info: instFooNat
---
trace: [Meta.synthInstance.cache] new: Foo ?m
[Meta.synthInstance.cache] stuck (cached): Foo ?m
[Meta.synthInstance.cache] new: Foo Nat
-/
#guard_msgs in
run_meta do
  let m ← mkFreshExprMVar (mkSort .one) (userName := `m)
  let type := mkApp (mkConst ``Foo) m
  synth type
  synth type
  m.mvarId!.assign (mkConst ``Nat)
  synth (← instantiateMVars type)

-- Stuck on a metavariable in the type of a local instance: the key does not change when the
-- metavariable is assigned, so such a query is not memoized.
/--
info: stuck
---
info: inst
---
trace: [Meta.synthInstance.cache] new: Foo Nat
[Meta.synthInstance.cache] new: Foo Nat
-/
#guard_msgs in
run_meta do
  let m ← mkFreshExprMVar (mkSort .one)
  withLocalDeclD `inst (mkApp (mkConst ``Foo) m) fun _ => do
    let type := mkApp (mkConst ``Foo) (mkConst ``Nat)
    synth type
    m.mvarId!.assign (mkConst ``Nat)
    synth type

-- A local declaration replaced under the same `FVarId` invalidates the memo.
/--
info: stuck
---
info: stuck
---
trace: [Meta.synthInstance.cache] new: Baz ?m
[Meta.synthInstance.cache] new: Baz ?m
-/
#guard_msgs in
run_meta do
  let m ← mkFreshExprMVar (mkSort .one) (userName := `m)
  withLocalDeclD `inst (mkApp (mkConst ``Foo) (mkConst ``Nat)) fun inst => do
    let type := mkApp (mkConst ``Baz) m
    synth type
    let lctx := (← getLCtx).modifyLocalDecl inst.fvarId!
      (·.setType (mkApp (mkConst ``Foo) (mkConst ``Int)))
    withLCtx lctx (← getLocalInstances) do
      synth type
