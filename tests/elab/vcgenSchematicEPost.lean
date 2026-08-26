import Std.Tactic.Do
import Std.WP

/-!
Tests that `vcgen` keeps the exception postcondition of a spec that states it as `estack⟨E⟩` with `E`
schematic, that a spec stating `⊥` still weakens without emitting an exception postcondition
verification condition, and that a goal stating `⊤` closes the projected exception postcondition
`⊤.fst e` outright.
-/

set_option experimental.vcgen true
open Std.WP Lean.Order

abbrev M := ExceptT String Id

axiom Q : String → Prop

def boom : M Unit := throw "boom"

def boom' : M Unit := throw "boom"

def boomBot : M Unit := throw "boom"

/-- Exception postcondition stated as `estack⟨E⟩` with `E` schematic. -/
@[spec] theorem boom_spec {E : String → Prop} :
    ⦃E "boom"⦄ boom ⦃fun _ => True; estack⟨E⟩⦄ := ⟨PartialOrder.rel_refl⟩

/-- Exception postcondition stated as a whole schematic stack. -/
@[spec] theorem boom'_spec {E : EStack⟨String → Prop⟩} :
    ⦃E.fst "boom"⦄ boom' ⦃fun _ => True; E⦄ := ⟨PartialOrder.rel_refl⟩

/-- Exception postcondition stated as `⊥`. -/
@[spec] axiom boomBot_spec : ⦃True⦄ boomBot ⦃fun _ => True; ⊥⦄

example : ⦃Q "boom"⦄ boom ⦃fun _ => True; estack⟨Q⟩⦄ := by
  vcgen

example : ⦃Q "boom"⦄ boom' ⦃fun _ => True; estack⟨Q⟩⦄ := by
  vcgen

/-- Whole-stack-schematic spec derived by `vcgen`: the rigid projection `E.fst "boom"` falls through
the `Prod.fst` lattice split to the lifted hypothesis. -/
theorem boom'_spec' {E : EStack⟨String → Prop⟩} :
    ⦃E.fst "boom"⦄ boom' ⦃fun _ => True; E⦄ := by
  vcgen

example : ⦃True⦄ boomBot ⦃fun _ => True; estack⟨Q⟩⦄ := by
  vcgen

/-- Goal exception postcondition `⊤`: the throw site's `⊤.fst "boom"` closes via `le_top`. -/
example : ⦃True⦄ (throw "boom" : M Unit) ⦃fun _ => True; ⊤⦄ := by
  vcgen
