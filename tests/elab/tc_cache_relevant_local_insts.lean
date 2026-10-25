import Lean

/-!
Tests that type class resolution results are shared between contexts whose local instances differ
only in classes the search did not consult, and not shared when a local instance of a consulted
class is added (it would be tried before the global instances).
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
