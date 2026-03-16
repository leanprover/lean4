import Lean
import VCGen

open Lean Meta Elab Tactic Sym Std Do SpecAttr

namespace MatchSplitState

set_option mvcgen.warning false

abbrev M := ExceptT String <| StateM Nat

@[spec high]
theorem Spec.throw_M {e : String} :
    ⦃Q.2.1 e⦄ throw (m := M) e ⦃Q⦄ := by
  mvcgen

@[spec high]
theorem Spec.set_M {s : Nat} :
    ⦃fun _ => Q.1 ⟨⟩ s⦄ set (m := M) s ⦃Q⦄ := by
  mvcgen

@[spec high]
theorem Spec.get_M :
    ⦃fun s => Q.1 s s⦄ get (m := M) ⦃Q⦄ := by
  mvcgen

/-- Matches on state `s` — the discriminant IS the excess state arg. -/
def step : M Unit := do
  let s ← get
  match s with
  | 0 => throw "s is zero"
  | n+1 => set n

def loop (n : Nat) : M Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step; loop n

def Goal (n : Nat) : Prop := ⦃fun s => ⌜s = n⌝⦄ loop n ⦃⇓_ s => ⌜s = 0⌝⦄

end MatchSplitState
