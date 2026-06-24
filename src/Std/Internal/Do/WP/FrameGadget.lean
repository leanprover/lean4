/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.WP.Frame
universe u v w z
@[expose] public section

set_option linter.missingDocs true

open Lean.Order

namespace Std.Internal.Do

namespace WP

variable {Prog : Type u} {Value : Type v} {Pred : Type w} {EPred : Type z}
  [Assertion Pred] [Assertion EPred] [WP Prog Value Pred EPred]

/-- Marks the residual program of an applied frame so `frames` patterns do not re-match it.
Stripped by `vcgen` before the real spec applies. -/
def skipFrame {α : Sort u} (a : α) : α := a

/-- `meet_wp_imp_le_wp` with the residual program wrapped in `skipFrame`, the per-call spec `vcgen`
applies for a framed program. The frame `F` is the first explicit argument so that `vcgen` can
partially apply it (pinning `F`) and feed the result through the ordinary spec machinery, leaving
`x`, `epost`, `Q`, and `hframe` schematic. -/
theorem meet_wp_imp_le_wp_skipFrame [Frame Pred] (F : Pred) (x : Prog)
  (epost : EPred) (Q : Value → Pred)
    (hframe : Preserving x (F ⊓ ·)) :
    F ⊓ wp (skipFrame x) (fun a => F ⇨ Q a) epost ⊑ wp x Q epost :=
  meet_wp_imp_le_wp (Q := Q) hframe

end WP

end Std.Internal.Do
