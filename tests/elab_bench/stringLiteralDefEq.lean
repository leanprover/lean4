module

public import Lean

/-!
Regression benchmark for #15985: elaborating `rfl` and repeating `isDefEq` when comparing a
string literal with `String.ofList` should take time linear in the string length.
-/

open Lean Elab Command Meta

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

elab "string_literal_defeq" : command => do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 16384 else 256
  let mut x : UInt64 := 1
  let mut chars := #[]
  for _ in [0:n] do
    x := x * 6364136223846793005 + 1442695040888963407
    chars := chars.push (Nat.toDigits 16 (x >>> 60).toNat).head!
  elabCommand (← `(def $(mkIdent `str) : String := $(quote (String.ofList chars.toList))))
  let elems : Array Term := chars.map fun c => ⟨Syntax.mkCharLit c⟩
  elabCommand (← `(noncomputable def $(mkIdent `chars) : List Char := [$elems,*]))

string_literal_defeq

theorem literal_eq_list : str = String.ofList chars := rfl

run_meta do
  for _ in [0:2] do
    unless ← isDefEq (mkConst ``str) (mkApp (mkConst ``String.ofList) (mkConst ``chars)) do
      throwError "string literal and character list are not definitionally equal"
