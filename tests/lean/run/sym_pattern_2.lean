import Lean.Meta.Sym
open Lean Meta Sym Grind
set_option grind.debug true
opaque p [Ring α] : α → α → Prop
axiom pax [CommRing α] [NoNatZeroDivisors α] (x y : α) : p x y → p (y + 1) x
opaque a : Int
opaque b : Int
def ex₁ := p (a + 1) b

def test₁ : SymM Unit := do
  let pEx ← mkPatternFromDecl ``pax
  let e ← shareCommon (← getConstInfo ``ex₁).value!
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
#eval SymM.run' test₁

theorem mk_forall_and (P Q : α → Prop) : (∀ x, P x) → (∀ x, Q x) → (∀ x, P x ∧ Q x) := by
  grind

opaque q : Nat → Nat → Prop
opaque f : Nat → Nat

def ex₂ := ∀ x, q x 0 ∧ q (f (f x)) (f x + f (f 1))

def test₂ : SymM Unit := do
  /- We use `some 5` because we want the pattern to be `(∀ x, ?P x ∧ ?Q x)`-/
  let p ← mkPatternFromDecl ``mk_forall_and (some 5)
  let e ← shareCommon (← getConstInfo ``ex₂).value!
  logInfo p.pattern
  logInfo e
  let some r₁ ← p.unify? e | throwError "failed"
  let h := mkAppN (mkConst ``mk_forall_and r₁.us) r₁.args
  check h
  logInfo h
  logInfo (← Sym.inferType r₁.args[3]!)
  logInfo (← Sym.inferType r₁.args[4]!)

/--
info: ∀ (x : #4), @#3 x ∧ @#2 x
---
info: ∀ (x : Nat), q x 0 ∧ q (f (f x)) (f x + f (f 1))
---
info: mk_forall_and (fun x => q x 0) (fun x => q (f (f x)) (f x + f (f 1))) ?m.4 ?m.5
---
info: ∀ (x : Nat), q x 0
---
info: ∀ (x : Nat), q (f (f x)) (f x + f (f 1))
-/
#guard_msgs in
#eval SymM.run' test₂
