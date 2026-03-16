import Lean
import VCGen

open Lean Meta Elab Tactic Sym Std Do SpecAttr

namespace PurePrecond

set_option mvcgen.warning false

def flipp (_ : Bool) : StateM Bool Unit := modify not

theorem Spec.flipp_false :
    ⦃fun b => ⌜b = false⌝⦄ flipp false ⦃⇓ _ b => ⌜b = true⌝⦄ := by
  mvcgen [flipp] <;> grind

theorem Spec.flipp_true :
    ⦃fun b => ⌜b = true⌝⦄ flipp true ⦃⇓ _ b => ⌜b = false⌝⦄ := by
  mvcgen [flipp] <;> grind

attribute [spec] Spec.flipp_true Spec.flipp_false

def step : StateM Bool Unit := do
  flipp true
  flipp false

def loop (n : Nat) : StateM Bool Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step; loop n

def Goal (n : Nat) : Prop := ⦃fun b => ⌜b = true⌝⦄ loop n ⦃⇓ _ b => ⌜b = true⌝⦄

end PurePrecond
