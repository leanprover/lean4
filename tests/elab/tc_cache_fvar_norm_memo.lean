import Lean

/-!
Tests that cached results are not served after what the free-variable normalization of their
context saw has changed: a metavariable assignment that was reverted, or a local declaration that was
replaced under the same `FVarId`. In both cases a stale normalization (e.g. one memoized by an
earlier query) would yield the cache key of `[inst : Foo Nat] ⊢ Baz` and serve its instance.
-/

open Lean Meta

class Foo (α : Type) where
class Baz where
class Qux where
instance [Foo Nat] : Baz := ⟨⟩
instance : Qux := ⟨⟩

/-- Synthesizes `Baz` under `[inst : Foo Nat]`, which stores the result under the normalized key. -/
def synthBazUnderFooNat : MetaM Unit :=
  withLocalDeclD `inst (mkApp (mkConst ``Foo) (mkConst ``Nat)) fun inst =>
    withNewLocalInstances #[inst] 0 do
      logInfo m!"[inst : Foo Nat] ⊢ Baz: {← synthInstance? (mkConst ``Baz)}"

/--
info: [inst : Foo Nat] ⊢ Baz: instBazOfFooNat
---
info: [inst : Foo Int] ⊢ Baz: <not-available>
-/
#guard_msgs in
run_meta do
  synthBazUnderFooNat
  let α ← mkFreshExprMVar (mkSort .one)
  withLocalDeclD `inst (mkApp (mkConst ``Foo) α) fun inst =>
    withNewLocalInstances #[inst] 0 do
      let s ← saveState
      α.mvarId!.assign (mkConst ``Nat)
      -- an earlier query under `inst : Foo Nat`
      discard <| synthInstance? (mkConst ``Qux)
      s.restore
      α.mvarId!.assign (mkConst ``Int)
      logInfo m!"[inst : Foo Int] ⊢ Baz: {← synthInstance? (mkConst ``Baz)}"

/--
info: [inst : Foo Nat] ⊢ Baz: instBazOfFooNat
---
info: [inst : Foo Int] ⊢ Baz: <not-available>
-/
#guard_msgs in
run_meta do
  synthBazUnderFooNat
  withLocalDeclD `inst (mkApp (mkConst ``Foo) (mkConst ``Nat)) fun inst =>
    withNewLocalInstances #[inst] 0 do
      -- an earlier query under `inst : Foo Nat`
      discard <| synthInstance? (mkConst ``Qux)
      let lctx := (← getLCtx).modifyLocalDecl inst.fvarId!
        (·.setType (mkApp (mkConst ``Foo) (mkConst ``Int)))
      withLCtx lctx (← getLocalInstances) do
        logInfo m!"[inst : Foo Int] ⊢ Baz: {← synthInstance? (mkConst ``Baz)}"
