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
opaque G : Type → Type

/--
Synthesizes `Bar α` under fresh `α : Type`, `inst : Foo α` and `aux : C (G ?m)`, with `?m := α` if
`assign`. The search for `Bar α` consults the local instances of `Foo`, so `aux` is in the
normalization closure for `C := Foo` and not for `C := Aux`.
-/
def synthBar (assign : Bool) (C : Name) : MetaM Unit :=
  withLocalDeclD `α (mkSort .one) fun α =>
  withLocalDeclD `inst (mkApp (mkConst ``Foo) α) fun _ => do
    let m ← mkFreshExprMVar (mkSort .one)
    withLocalDeclD `aux (mkApp (mkConst C) (mkApp (mkConst ``G) m)) fun _ => do
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
  synthBar (assign := true) ``Foo
  synthBar (assign := true) ``Foo

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
  synthBar (assign := false) ``Foo
  synthBar (assign := false) ``Foo

-- The search does not consult the local instances of `Aux`, so `aux` is not in the closure, and the
-- contexts are shared even with `?m` unassigned.
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
  synthBar (assign := false) ``Aux
  synthBar (assign := false) ``Aux
