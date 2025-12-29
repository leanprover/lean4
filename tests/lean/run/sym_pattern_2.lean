import Lean.Meta.Sym
open Lean Meta Sym Grind
set_option grind.debug true
opaque p [Ring α] : α → α → Prop
axiom pax [CommRing α] [NoNatZeroDivisors α] (x y : α) : p x y → p (y + 1) x
opaque a : Int
opaque b : Int
def ex := p (a + 1) b

def test : SymM Unit := do
  let pEx ← mkPatternFromTheorem ``pax
  let e ← shareCommon (← getConstInfo ``ex).value!
  let some r₁ ← pEx.match? e | throwError "failed"
  let h := mkAppN (mkConst ``pax r₁.us) r₁.args
  check h
  logInfo h
  logInfo r₁.args

/--
info: pax b a ?m.1
---
info: #[Int, instCommRingInt, instNoNatZeroDivisorsInt, b, a, ?m.1]
-/
#guard_msgs in
#eval SymM.run' test
