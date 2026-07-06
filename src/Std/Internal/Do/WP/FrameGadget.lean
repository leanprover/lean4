/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.WP.Frame
universe u v w z r
@[expose] public section

set_option linter.missingDocs true

open Lean.Order

namespace Std.Internal.Do.Gadget

variable {Prog : Type u} {Value : Type v} {Pred : Type w} {EPred : Type z}
  [Assertion Pred] [Assertion EPred] [WP Prog Value Pred EPred]

/-- Marks an already-framed program so `frames` patterns do not re-match it.
Stripped by `vcgen` before the real spec applies. -/
def skipFrame {α : Sort u} (a : α) : α := a

/-- The per-call spec `vcgen` applies for a framed program: for a frame operator `conj` whose slices
preserve `Sup`, framing by `F` runs the program under the upper adjoint of `conj F` and re-applies
`conj F`. `conj` is the first explicit argument so that `vcgen` can pin it (to the inferred frame
operator) while leaving `F`, `x`, `E`, `Q`, and `hframes` schematic. The lattice meet is the instance
`conj := (· ⊓ ·)`, whose residual `vcgen` folds to Heyting `⇨`. -/
theorem op_wp_upperAdjoint_le_wp_skipFrame {R : Type r} (conj : R → Pred → Pred)
  [∀ r, PreservesSup (conj r)] (F : R) (x : Prog) (E : EPred) (Q : Value → Pred)
    (hframes : WP.Frames conj x F) :
    conj F (wp (skipFrame x) (fun a => PreservesSup.upperAdjoint (conj F) (Q a)) E) ⊑ wp x Q E :=
  hframes.op_wp_upperAdjoint_le_wp _ _ _

end Std.Internal.Do.Gadget
