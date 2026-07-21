/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Data.Function
public import Init.NotationExtra
import Init.Classical
public section
namespace Lean.Grind
open Function

noncomputable def leftInv {α : Sort u} {β : Sort v} (f : α → β) (hf : Injective f) [Nonempty α] : β → α :=
  Classical.choose hf.exists_leftInverse

theorem leftInv_eq {α : Sort u} {β : Sort v} (f : α → β) (hf : Injective f) [Nonempty α] (a : α) : leftInv f hf (f a) = a :=
  Classical.choose_spec hf.exists_leftInverse a

@[app_unexpander leftInv]
meta def leftInvUnexpander : PrettyPrinter.Unexpander := fun stx => do
  match stx with
  | `($_ $f:term $_) => `($f⁻¹)
  | `($_ $f:term $_ $a:term) => `($f⁻¹ $a)
  | _ => throw ()

end Lean.Grind
