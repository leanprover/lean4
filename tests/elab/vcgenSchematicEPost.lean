import Std.Tactic.Do
import Std.WP

/-!
Tests that `vcgen` keeps the exception postcondition of a spec that states it as `epost⟨E⟩` with `E`
schematic, and that a spec stating `⊥` still weakens without emitting an exception postcondition
verification condition.
-/

set_option mvcgen.warning false
open Std.WP Lean.Order

abbrev M := ExceptT String Id

axiom Q : String → Prop

def boom : M Unit := throw "boom"

def boom' : M Unit := throw "boom"

def boomBot : M Unit := throw "boom"

/-- Exception postcondition stated as `epost⟨E⟩` with `E` schematic. -/
@[spec] theorem boom_spec {E : String → Prop} :
    ⦃E "boom"⦄ boom ⦃fun _ => True; epost⟨E⟩⦄ := ⟨PartialOrder.rel_refl⟩

/-- Exception postcondition stated as a whole schematic `EPost`. -/
@[spec] theorem boom'_spec {E : EPost⟨String → Prop⟩} :
    ⦃E.head "boom"⦄ boom' ⦃fun _ => True; E⦄ := ⟨PartialOrder.rel_refl⟩

/-- Exception postcondition stated as `⊥`. -/
@[spec] axiom boomBot_spec : ⦃True⦄ boomBot ⦃fun _ => True; ⊥⦄

example : ⦃Q "boom"⦄ boom ⦃fun _ => True; epost⟨Q⟩⦄ := by
  vcgen

example : ⦃Q "boom"⦄ boom' ⦃fun _ => True; epost⟨Q⟩⦄ := by
  vcgen

example : ⦃True⦄ boomBot ⦃fun _ => True; epost⟨Q⟩⦄ := by
  vcgen
