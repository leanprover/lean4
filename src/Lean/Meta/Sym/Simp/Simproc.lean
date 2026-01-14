/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
public import Lean.Meta.Sym.Simp.Result
namespace Lean.Meta.Sym.Simp

public abbrev Simproc.andThen (f g : Simproc) : Simproc := fun e₁ => do
  let r ← f e₁
  match r with
  | .step _ _ true | .rfl true  => return r
  | .rfl false => g e₁
  | .step e₂ h₁ false => mkEqTransResult e₁ e₂ h₁ (← g e₂)

public instance : AndThen Simproc where
  andThen f g := Simproc.andThen f (g ())

end Lean.Meta.Sym.Simp
