import Lean

/-!
A failed redeclaration does not replace the declaration ranges of the existing declaration of the
same name: the first report of a declaration's ranges wins.
-/

open Lean

def T1 := 20

/-- error: `T1` has already been declared -/
#guard_msgs in
inductive T1 : Type
  | bla : T1

def S1 := 20

/-- error: `S1` has already been declared -/
#guard_msgs in
structure S1 where
  x : Nat

/-- Line on which the declaration ranges of `declName` start. -/
def rangeLine (declName : Name) : CoreM Nat := do
  let some ranges ← findDeclarationRanges? declName | throwError "no ranges for `{declName}`"
  return ranges.range.pos.line

/-- info: 10, 17 -/
#guard_msgs in
#eval show CoreM Unit from do
  logInfo m!"{← rangeLine ``T1}, {← rangeLine ``S1}"
