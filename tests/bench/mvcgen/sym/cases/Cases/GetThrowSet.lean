import Lean
import VCGen

open Lean Meta Elab Tactic Sym Std Do SpecAttr

namespace GetThrowSet

set_option mvcgen.warning false
set_option backward.do.legacy false -- exercises asymmetric bind depth from new do elaborator

abbrev M := ExceptT String <| StateM Nat

-- Partially evaluated specs for best performance.

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

def step (lim : Nat) : M Unit := do
  let s ← get
  if s > lim then
    throw "s is too large"
  set (s + 1)

def loop (n : Nat) : M Unit := do
  match n with
  | 0 => pure ()
  | n+1 => loop n; step n

def Goal (n : Nat) : Prop := ⦃fun s => ⌜s = 0⌝⦄ loop n ⦃⇓_ s => ⌜s = n⌝⦄

end GetThrowSet
