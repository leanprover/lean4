import Lean

/-!
Tests that type class resolution results are shared between contexts whose local instances differ
only in classes the search did not consult, and not shared when a local instance of a consulted
class is added (it would be tried before the global instances). Such results persist across
commands, and queries with output parameters are shared in the same way.
-/

open Lean Meta

class Foo (α : Type) where
class Bar (α : Type) where
class Unrelated (α : Type) where
instance : Foo Nat := ⟨⟩
instance [Foo α] : Bar α := ⟨⟩

/-- Synthesizes `Bar Nat` under a fresh local instance of type `localType`. -/
def synthBarUnder (localType : Expr) : MetaM Unit :=
  withLocalDeclD `inst localType fun _ =>
    withOptions (·.setBool `trace.Meta.synthInstance.cache true) do
      logInfo m!"{← synthInstance? (mkApp (mkConst ``Bar) (mkConst ``Nat))}"

-- `Unrelated` is never consulted: the second query is served by the entry the first one stored.
/--
info: instBarOfFoo
---
info: instBarOfFoo
---
trace: [Meta.synthInstance.cache] new: Bar Nat
[Meta.synthInstance.cache] cached: Bar Nat
-/
#guard_msgs in
run_meta do
  synthBarUnder (mkApp (mkConst ``Unrelated) (mkConst ``Nat))
  synthBarUnder (mkApp (mkConst ``Unrelated) (mkConst ``Int))

-- A local instance of `Foo`, which the search consults, is tried first and changes the answer.
/--
info: @instBarOfFoo Nat inst
---
trace: [Meta.synthInstance.cache] new: Bar Nat
-/
#guard_msgs in
run_meta do
  withLocalDeclD `inst (mkApp (mkConst ``Foo) (mkConst ``Nat)) fun _ =>
    withOptions (fun o => (o.setBool `trace.Meta.synthInstance.cache true).setBool `pp.explicit true) do
      logInfo m!"{← synthInstance? (mkApp (mkConst ``Bar) (mkConst ``Nat))}"

-- The entry for `Bar α` under `[Foo α]` persists: a later declaration with the same instance
-- binders, up to renaming, is served from it.
set_option trace.Meta.synthInstance.cache true in
/-- trace: [Meta.synthInstance.cache] new: Bar α -/
#guard_msgs in
def p1 {α : Type} [Foo α] : Unit := let _ : Bar α := inferInstance; ()

set_option trace.Meta.synthInstance.cache true in
/-- trace: [Meta.synthInstance.cache] cached: Bar β -/
#guard_msgs in
def p2 {β : Type} [Foo β] [Unrelated β] : Unit := let _ : Bar β := inferInstance; ()

class Out (α : Type) (β : outParam Type) where
instance : Out Nat Int := ⟨⟩

/-- Synthesizes `Out Nat ?β` under a fresh local instance of type `localType`. -/
def synthOutUnder (localType : Expr) : MetaM Unit :=
  withLocalDeclD `inst localType fun _ => do
    let β ← mkFreshExprMVar (mkSort .one)
    let opts (o : Options) :=
      (o.setBool `trace.Meta.synthInstance.cache true).setBool `pp.mvars.anonymous false
    withOptions opts do
      logInfo m!"{← synthInstance? (mkApp2 (mkConst ``Out) (mkConst ``Nat) β)}"

-- The output parameter is a wildcard in the key, so the query is shared like `Bar Nat` above.
/--
info: instOutNatInt
---
info: instOutNatInt
---
trace: [Meta.synthInstance.cache] new: Out Nat ?_
[Meta.synthInstance.cache] cached: Out Nat ?_
-/
#guard_msgs in
run_meta do
  synthOutUnder (mkApp (mkConst ``Unrelated) (mkConst ``Nat))
  synthOutUnder (mkApp (mkConst ``Unrelated) (mkConst ``Int))
