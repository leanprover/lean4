import Lean.Meta.Sym
open Lean Meta Sym

opaque p : Nat → Prop
opaque q : Nat → Nat → Prop

def ex := ∃ x : Nat, p x ∧ x = .zero

def test : SymM Unit := do
  let pEx ← mkPatternFromTheorem ``Exists.intro
  let pAnd ← mkPatternFromTheorem ``And.intro
  let pEq ← mkPatternFromTheorem ``Eq.refl
  let e := (← getConstInfo ``ex).value!
  let some r₁ ← pEx.match? e | throwError "failed"
  logInfo <| mkAppN (mkConst ``Exists.intro r₁.us) r₁.args
  let some r₂ ← pAnd.match? (← inferType r₁.args[3]!) | throwError "failed"
  logInfo <| mkAppN (mkConst ``And.intro r₂.us) r₂.args
  let some r₃ ← pEq.unify? (← inferType r₂.args[3]!) | throwError "failed"
  logInfo <| mkAppN (mkConst ``Eq.refl r₃.us) r₃.args

/--
info: @Exists.intro Nat (fun x => And (p x) (@Eq Nat x Nat.zero)) ?m.1 ?m.2
---
info: @And.intro (p ?m.1) (@Eq Nat ?m.1 Nat.zero) ?m.3 ?m.4
---
info: @Eq.refl Nat Nat.zero
-/
#guard_msgs in
set_option pp.explicit true in
#eval SymM.run' test
