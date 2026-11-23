module
meta import Lean.Elab.DeclNameGen

open Lean Elab Command

/-!
Tests for the `mkInstanceNameOfType` function
-/

public structure Public.A where
public structure Public'.A where

private structure Private.B where
public structure Public.B where

public structure Private.C where
private structure Public.C where

private structure Private.D where
private structure Private'.D where

meta def allNames : Array Name := #[
  ``Public.A,
  ``Public'.A,

  ``Private.B,
  ``Public.B,

  ``Public.C,
  ``Private.C,

  ``Private.D,
  ``Private'.D,
]

meta def assertNodup (xs : Array Name) : MetaM (Array Name) := do
  assert! xs.toList.Nodup
  return xs

/-!
`mkInstanceNameOfType` avoids collisions with the same name, its private version and its
non-private version...
-/

namespace Individually

/-!
... when each "instance" is declared directly after generating the name
-/

meta def declareInst (type : Expr) : MetaM Name := do
  let name ← mkInstanceNameOfType type
  addDecl <| .axiomDecl <| { name, type, levelParams := [], isUnsafe := false }
  return privateToUserName name

/--
info: #[`Individually.instBEqA, `Individually.instBEqA_1, `Individually.instBEqB, `Individually.instBEqB_1,
  `Individually.instBEqC, `Individually.instBEqC_1, `Individually.instBEqD, `Individually.instBEqD_1]
-/
#guard_msgs in
#eval do
  assertNodup <| ← allNames.mapM fun name =>
    declareInst (.app (.const ``BEq [0]) (.const name []))

end Individually

namespace AllAtOnce

/-!
... when all names are generated at once and the `additionalConstants` parameter of
`hasNameCollision` is used to pass the previous names in the loop
-/

meta def declareInsts (types : Array Expr) : MetaM (Array Name) := do
  let mut names := #[]
  for type in types do
    let name ← mkInstanceNameOfType type (hasNameCollision · · names.contains)
    names := names.push name
  for name in names, type in types do
    addDecl <| .axiomDecl <| { name, type, levelParams := [], isUnsafe := false }
  return names.map privateToUserName

/--
info: #[`AllAtOnce.instBEqA, `AllAtOnce.instBEqA_1, `AllAtOnce.instBEqB, `AllAtOnce.instBEqB_1, `AllAtOnce.instBEqC,
  `AllAtOnce.instBEqC_1, `AllAtOnce.instBEqD, `AllAtOnce.instBEqD_1]
-/
#guard_msgs in
#eval do
  assertNodup <| ← declareInsts <| allNames.map fun name =>
    .app (.const ``BEq [0]) (.const name [])

end AllAtOnce
