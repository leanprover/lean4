module

public meta import Lean

/-!
Tests `newtype` under the module system: whether the bodies of the generated constructor and
projector are exposed to importing modules follows whatever the `def` elaborator decided for the
type itself, since importers can only reduce `N.proj (N.mk a)` in the kernel if all three bodies are
visible.
-/

@[expose] public newtype Exposed := Nat with toNat
newtype Priv := Nat with toNat

open Lean in
run_meta do
  let env ← getEnv
  for n in [``Exposed, ``Exposed.mk, ``Exposed.toNat] do
    unless env.hasExposedBody n do throwError "expected {n} to be exposed"
  for n in [``Priv, ``Priv.mk, ``Priv.toNat] do
    if env.hasExposedBody n then throwError "expected {n} not to be exposed"

example (n : Nat) : Exposed.toNat (Exposed.mk n) = n := rfl
example (x : Priv) : Priv.mk (Priv.toNat x) = x := rfl
