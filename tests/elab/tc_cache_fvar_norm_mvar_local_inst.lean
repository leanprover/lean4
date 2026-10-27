import Lean

/-!
Tests that the type class resolution cache does not normalize free variables under a local instance
whose `fvar` is not a free variable, as `LocalInstance.fvar` allows (#15858). The `Lean.Meta.Deriving`
framework adds its instance hypotheses as local instances that are metavariables.

The normalization follows the free variables of each local instance to their types. The type of a
metavariable `?h : Foo α` mentions `α` although `?h` does not, so normalizing would give `Foo β` and
`Foo α` the same key, and the failure cached for `Foo β` would be served for `Foo α`.
-/

open Lean Meta

class Foo (α : Type) where

/--
Synthesizes `Foo β` and then `Foo α` under fresh `α β : Type` and a local instance `h : Foo α`. The
local instance is the metavariable `?h` if `mvar` is set and a free variable otherwise.
-/
def synthBetaThenAlpha (mvar : Bool) : MetaM Unit :=
  withLocalDeclD `α (mkSort 1) fun α =>
  withLocalDeclD `β (mkSort 1) fun β => do
    let k : MetaM Unit :=
      withOptions (·.setBool `trace.Meta.synthInstance.cache true) do
        for ty in [β, α] do
          let r ← synthInstance? (mkApp (mkConst ``Foo) ty)
          logInfo m!"Foo {ty} ↦ {r.getD (mkConst `failed)}"
    let type := mkApp (mkConst ``Foo) α
    if mvar then
      let h ← mkFreshExprMVar type .syntheticOpaque `h
      withLCtx (← getLCtx) ((← getLocalInstances).push { className := ``Foo, fvar := h }) k
    else
      withLocalDeclD `h type fun _ => k

/--
info: Foo β ↦ failed
---
info: Foo α ↦ h
---
trace: [Meta.synthInstance.cache] new: Foo β
[Meta.synthInstance.cache] new: Foo α
-/
#guard_msgs in
run_meta synthBetaThenAlpha (mvar := false)

/--
info: Foo β ↦ failed
---
info: Foo α ↦ ?h
---
trace: [Meta.synthInstance.cache] new: Foo β
[Meta.synthInstance.cache] new: Foo α
-/
#guard_msgs in
set_option debug.synthInstance.checkCacheHits true in
run_meta synthBetaThenAlpha (mvar := true)
