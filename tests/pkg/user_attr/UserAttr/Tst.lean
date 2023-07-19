import Lean
import UserAttr.BlaAttr

@[bla] def f (x : Nat) := x + 2
@[bla] def g (x : Nat) := x + 1

@[foo 10] def h1 (x : Nat) := 2*x + 1
@[foo 20 important] def h2 (x : Nat) := 2*x + 1

open Lean in
def hasBlaAttr (declName : Name) : CoreM Bool :=
  return blaAttr.hasTag (← getEnv) declName

#eval hasBlaAttr ``f
#eval hasBlaAttr ``id

open Lean in
def getFooAttrInfo? (declName : Name) : CoreM (Option (Nat × Bool)) :=
  return fooAttr.getParam? (← getEnv) declName

#eval getFooAttrInfo? ``f
#eval getFooAttrInfo? ``h1
#eval getFooAttrInfo? ``h2

@[my_simp] theorem f_eq : f x = x + 2 := rfl
@[my_simp] theorem g_eq : g x = x + 1 := rfl

example : f x + g x = 2*x + 3 := by
  fail_if_success simp_arith -- does not appy f_eq and g_eq
  simp_arith [f, g]

example : f x + g x = 2*x + 3 := by
  simp_arith [my_simp]

example : f x = id (x + 2) := by
  simp
  simp [my_simp]

macro "my_simp" : tactic => `(tactic| simp [my_simp])

example : f x = id (x + 2) := by
  my_simp

@[simp low, my_simp low]
axiom expand_mul_add (x y z : Nat) : x * (y + z) = x * y + x * y
@[simp high, my_simp high]
axiom expand_add_mul (x y z : Nat) : (x + y) * z = x * z + y * z
@[simp, my_simp]
axiom lassoc_add (x y z : Nat) : x + (y + z) = x + y + z

set_option trace.Meta.Tactic.simp.rewrite true

-- Rewrites: expand_mul_add -> expand_mul_add -> lassoc_add
theorem ex1 (x : Nat) : (x + x) * (x + x) = x * x + x * x + x * x + x * x := by simp only [my_simp]

-- Rewrites: expand_add_mul -> expand_mul_add -> lassoc_add
theorem ex2 (x : Nat) : (x + x) * (x + x) = x * x + x * x + x * x + x * x := by simp

open Lean Meta in
def checkProofs : MetaM Unit := do
  let .thmInfo info1 ← getConstInfo `ex1 | throwError "unexpected"
  let .thmInfo info2 ← getConstInfo `ex2 | throwError "unexpected"
  unless info1.value == info2.value do
    throwError "unexpected values"

#eval checkProofs

open Lean Meta in
def showThmsOf (simpAttrName : Name) : MetaM Unit := do
  let some simpExt ← getSimpExtension? simpAttrName
    | throwError "`{simpAttrName}` is not a simp attribute"
  let thms ← simpExt.getTheorems
  let thmNames := thms.lemmaNames.fold (init := #[]) fun acc origin => acc.push origin.key
  for thmName in thmNames do
    IO.println thmName

#eval showThmsOf `my_simp
