import Lean

/-!
Tests that a query mentioning a let-bound free variable is not shared between contexts by the
free-variable normalization of the type class resolution cache key. Definitional unfolding can see
a let value, which the normalized key does not record, so two contexts agreeing on the types of
their free variables but not on a let value are not interchangeable.
-/

open Lean Meta

class Bar (n : Nat) where
instance : Bar 1 := ⟨⟩

def synthBar (n : Expr) : MetaM Unit :=
  withOptions (·.setBool `trace.Meta.synthInstance.cache true) do
    logInfo m!"{← synthInstance? (mkApp (mkConst ``Bar) n)}"

-- Without a value, the two contexts only differ in the identity of `n` and share the entry.
/--
info: <not-available>
---
info: <not-available>
---
trace: [Meta.synthInstance.cache] new: Bar n
[Meta.synthInstance.cache] cached: Bar n
-/
#guard_msgs in
run_meta do
  withLocalDeclD `n (mkConst ``Nat) synthBar
  withLocalDeclD `n (mkConst ``Nat) synthBar

-- With a value, the contexts are not normalized, and thus not shared.
/--
info: instBarOfNatNat
---
info: instBarOfNatNat
---
trace: [Meta.synthInstance.cache] new: Bar n
[Meta.synthInstance.cache] new: Bar n
-/
#guard_msgs in
run_meta do
  withLetDecl `n (mkConst ``Nat) (mkNatLit 1) synthBar
  withLetDecl `n (mkConst ``Nat) (mkNatLit 1) synthBar

-- In particular, a context with a different value does not get the instance for `n := 1`.
/--
info: instBarOfNatNat
---
info: <not-available>
---
trace: [Meta.synthInstance.cache] new: Bar n
[Meta.synthInstance.cache] new: Bar n
-/
#guard_msgs in
run_meta do
  withLetDecl `n (mkConst ``Nat) (mkNatLit 1) synthBar
  withLetDecl `n (mkConst ``Nat) (mkNatLit 2) synthBar
