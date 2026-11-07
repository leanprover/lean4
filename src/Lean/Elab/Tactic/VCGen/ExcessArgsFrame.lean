/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Meta.Basic
import Lean.Meta.AppBuilder
import Std.Internal.Order.Heyting

open Lean Meta

namespace Lean.Elab.Tactic.VCGen

/--
The frames of a precondition `pre` for the excess state arguments `s₁ … sₙ` of a goal
`pre ⊑ X s₁ … sₙ`. For `n = 2`, `frames` is
`#[fun u₁ => ⌜u₁ = s₁⌝ ⊓ fun u₂ => ⌜u₂ = s₂⌝ ⊓ pre, fun u₂ => ⌜u₂ = s₂⌝ ⊓ pre, pre]`.
Its first entry `frame` holds at `s₁ s₂` exactly where `pre` holds, and is `⊥` at every other pair
of states, so `pre ⊑ X s₁ s₂` and `frame ⊑ X` are equivalent.
-/
public structure ExcessArgsFrameInfo where
  frames : Array Expr

/-- Build the frames of `pre` for the excess state arguments `ss`. -/
public def ExcessArgsFrameInfo.new (pre : Expr) (ss : Array Expr) : MetaM ExcessArgsFrameInfo := do
  let mut frames := #[pre]
  for s in ss.reverse do
    let r := frames.back!
    frames := frames.push <| ← withLocalDeclD `u (← Meta.inferType s) fun u => do
      let ofp ← mkAppOptM ``Lean.Order.CompleteLattice.ofProp
        #[← Meta.inferType r, none, ← mkEq u s]
      mkLambdaFVars #[u] (← mkAppM ``Lean.Order.meet #[ofp, r])
  return ⟨frames.reverse⟩

/-- The frame of `pre` for all excess state arguments. -/
public def ExcessArgsFrameInfo.frame (i : ExcessArgsFrameInfo) : Expr := i.frames[0]!

/-- Turn `h : frame ⊑ X` into a proof of `pre ⊑ X s₁ … sₙ`. -/
public def ExcessArgsFrameInfo.instantiate (i : ExcessArgsFrameInfo) (X : Expr) (ss : Array Expr)
    (h : Expr) : MetaM Expr := do
  let mut h := h
  for j in [0:ss.size] do
    h ← mkAppM ``Lean.Order.le_apply_of_point_meet_le
      #[ss[j]!, i.frames[j+1]!, mkAppN X (ss.take j), h]
  return h

/-- Turn `h : pre ⊑ X s₁ … sₙ` into a proof of `frame ⊑ X`. -/
public def ExcessArgsFrameInfo.abstract (i : ExcessArgsFrameInfo) (X : Expr) (ss : Array Expr)
    (h : Expr) : MetaM Expr := do
  let mut h := h
  for j in (List.range ss.size).reverse do
    h ← mkAppM ``Lean.Order.point_meet_le_of_le_apply
      #[ss[j]!, i.frames[j+1]!, mkAppN X (ss.take j), h]
  return h

end Lean.Elab.Tactic.VCGen
