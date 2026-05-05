/-
MWE: `mvcgen'` loses precondition facts in postcondition entailment VCs.
-/
import Cases
import Driver

open Lean Std Do

@[irreducible] def myFun (n : Nat) : StateM Nat Nat := return n

@[spec]
theorem myFun.spec (n : Nat) : ⦃fun _ => ⌜True⌝⦄ myFun n ⦃⇓ r _ => ⌜r = n⌝⦄ := by
  simp only [myFun, Triple]; intro s; exact SPred.pure_intro rfl

/--
trace: case vc2
s✝¹ : Nat
a✝² : s✝¹ = 42
a✝¹ s✝ : Nat
a✝ : a✝¹ = s✝¹
⊢ 42 = a✝¹
-/
#guard_msgs (trace) in
theorem fails : ⦃fun s => ⌜s = 42⌝⦄ (get >>= myFun) ⦃⇓ r _ => ⌜42 = r⌝⦄ := by
  mvcgen'
  trivial
  trace_state
  grind
