import Lean

/-!
Tests for the `[grind hom fallback]` modifier: a fallback rule is tried only when no other
homomorphism rule applies to the term. The toy type `W` has two images, `W.toInt` and `W.aux`,
related by the bridge `w.toInt = W.aux w`, and a direct rule for `W.add` into `Int`. As an
ordinary rule the bridge wins over the direct rule, since its left-hand side matches every
`toInt` term; as a fallback rule it applies only to the atoms.
-/

open Lean Meta Lean.Meta.Sym Lean.Meta.Sym.Simp

structure W where
  val : Int

def W.toInt (w : W) : Int := w.val
def W.aux (w : W) : Int := w.val
def W.add (a b : W) : W := ⟨a.val + b.val⟩

theorem W.toInt_add (a b : W) : (W.add a b).toInt = a.toInt + b.toInt := rfl
theorem W.toInt_eq_aux (w : W) : w.toInt = W.aux w := rfl

def applyHomo (declName : Name) : MetaM Unit := do
  let value := (← getConstInfoDefn declName).value
  lambdaTelescope value fun _ body => SymM.run do
    let thms ← Grind.getHomoTheorems
    let methods : Methods := { pre := thms.rewrite, post := thms.rewrite }
    let body ← share body
    let r ← simp body methods {}
    let result := Result.getResultExpr body r
    logInfo m!"{body}\n==>\n{result}"
    if let .step _ proof _ _ := r then
      Meta.check proof
      unless (← isDefEq (← Meta.inferType proof) (← mkEq body result)) do
        throwError "proof type mismatch"

def addToInt (a b : W) : Int := (W.add a b).toInt

attribute [grind hom] W.toInt_add

section OrdinaryBridge
attribute [local grind hom] W.toInt_eq_aux

/--
info: (a.add b).toInt
==>
(a.add b).aux
-/
#guard_msgs in
run_meta applyHomo ``addToInt
end OrdinaryBridge

section FallbackBridge
attribute [local grind hom fallback] W.toInt_eq_aux

/--
info: (a.add b).toInt
==>
a.aux + b.aux
-/
#guard_msgs in
run_meta applyHomo ``addToInt

example (a b : W) (h₁ : W.aux a = 1) (h₂ : W.aux b = 2) : (W.add a b).toInt = 3 := by grind
end FallbackBridge
