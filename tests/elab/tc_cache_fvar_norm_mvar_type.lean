import Lean

/-!
Tests that the type class resolution cache normalizes free variables when a variable in the
normalization closure has an assigned metavariable in its type, and does not when the metavariable
is unassigned. `Expr.hasMVar` stays set for assigned metavariables, so a syntactic check would give
up on the first kind as well.
-/

open Lean Meta

class Foo (α : Type) where
class Bar (α : Type) where
class Aux (α : Type) where
instance [Foo α] : Bar α := ⟨⟩

/--
Synthesizes `Bar α` under fresh `α : Type`, `inst : Foo α` and `aux : Aux ?m`, with `?m := α` if
`assign`.
-/
def synthBar (assign : Bool) : MetaM Unit :=
  withLocalDeclD `α (mkSort .one) fun α =>
  withLocalDeclD `inst (mkApp (mkConst ``Foo) α) fun _ => do
    let m ← mkFreshExprMVar (mkSort .one)
    withLocalDeclD `aux (mkApp (mkConst ``Aux) m) fun _ => do
      if assign then m.mvarId!.assign α
      withOptions (·.setBool `trace.Meta.synthInstance.cache true) do
        logInfo m!"{← synthInstance? (mkApp (mkConst ``Bar) α)}"

-- The second context differs from the first only in the identities of its variables.
/--
info: instBarOfFoo
---
info: instBarOfFoo
---
trace: [Meta.synthInstance.cache] new: Bar α
[Meta.synthInstance.cache] cached: Bar α
-/
#guard_msgs in
run_meta do
  synthBar (assign := true)
  synthBar (assign := true)

-- With `?m` unassigned, the contexts are not normalized, and thus not shared.
/--
info: instBarOfFoo
---
info: instBarOfFoo
---
trace: [Meta.synthInstance.cache] new: Bar α
[Meta.synthInstance.cache] new: Bar α
-/
#guard_msgs in
run_meta do
  synthBar (assign := false)
  synthBar (assign := false)
