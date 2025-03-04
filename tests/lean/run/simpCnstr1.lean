import Lean

open Lean in open Lean.Meta in
def test (declName : Name) : MetaM Unit := do
  let info ← getConstInfo declName
  forallTelescope info.type fun _ e => do
    let some (e', p) ← Simp.Arith.simp? e none | throwError "failed to simplify{indentExpr e}"
    check p
    unless (← isDefEq (← inferType p) (← mkEq e e')) do
      throwError "invalid proof"
    IO.println s!"{← Meta.ppExpr e} ==> {← Meta.ppExpr e'}"

axiom ex1 (a b : Nat) : a + b + 1 + a < b + 4 + a
axiom ex2 (a b : Nat) : a + b + 1 + a = b + 4 + a + b
axiom ex3 (a b : Nat) : 5 = b + 4 + a + b
axiom ex4 (a b : Nat) : 4 = 1 + a
axiom ex5 (a b : Nat) : 4 + ((a + a) + b) + (a + a) + (b + b) ≤ 3 + (4*a + b) + b + 8 + 1
axiom ex6 (a b : Nat) : 4 = 8 + a
axiom ex7 (a b : Nat) : a + a ≤ 8 + a + a + b
axiom ex8 (a b c d : Nat) : b + a + c + d ≤ a + b + a + b
axiom ex9 (a b : Nat) : a + b + 1 + a > b + 4 + a
axiom ex10 (a b : Nat) : a + b + 1 + a ≥ b + 4 + a
axiom ex11 (a b : Nat) : ¬ (a + b + 1 + a < b + 4 + a)
axiom ex12 (a b : Nat) : ¬ (a + b + 1 + a > b + 4 + a)
axiom ex13 (a b : Nat) : ¬ (a + b + 1 + a ≤ b + 4 + a)
axiom ex14 (a b c d : Nat) : ¬ (a + d + b + 1 + a + d ≥ b + 4 + a + c)

#eval test ``ex1
#eval test ``ex2
#eval test ``ex3
#eval test ``ex4
#eval test ``ex5
#eval test ``ex6
#eval test ``ex7
#eval test ``ex8
#eval test ``ex9
#eval test ``ex10
#eval test ``ex11
#eval test ``ex12
#eval test ``ex13
#eval test ``ex14
