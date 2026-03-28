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

theorem _root_.Function.Injective.leftInverse
    {α β} (f : α → β) (hf : Injective f) [hα : Nonempty α] :
    ∃ g : β → α, LeftInverse g f := by
  classical
  cases hα; next a0 =>
  let g : β → α := fun b =>
    if h : ∃ a, f a = b then Classical.choose h else a0
  exists g
  intro a
  have h : ∃ a', f a' = f a := ⟨a, rfl⟩
  have hfa : f (Classical.choose h) = f a := Classical.choose_spec h
  have : Classical.choose h = a := hf hfa
  simp [g, h, this]

noncomputable def leftInv {α : Sort u} {β : Sort v} (f : α → β) (hf : Injective f) [Nonempty α] : β → α :=
  Classical.choose (hf.leftInverse f)

theorem leftInv_eq {α : Sort u} {β : Sort v} (f : α → β) (hf : Injective f) [Nonempty α] (a : α) : leftInv f hf (f a) = a :=
  Classical.choose_spec (hf.leftInverse f) a

@[app_unexpander leftInv]
meta def leftInvUnexpander : PrettyPrinter.Unexpander := fun stx => do
  match stx with
  | `($_ $f:term $_) => `($f⁻¹)
  | `($_ $f:term $_ $a:term) => `($f⁻¹ $a)
  | _ => throw ()

end Lean.Grind
