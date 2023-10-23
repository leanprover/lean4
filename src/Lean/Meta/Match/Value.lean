/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr

namespace Lean.Meta

-- TODO: move?
private def UIntTypeNames : Array Name :=
  #[``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize]

private def isUIntTypeName (n : Name) : Bool :=
  UIntTypeNames.contains n

def isFinPatLit (e : Expr) : Bool :=
  e.isAppOfArity `Fin.ofNat 2 && e.appArg!.isNatLit

/-- Return `some (typeName, numLit)` if `v` is of the form `UInt*.mk (Fin.ofNat _ numLit)` -/
def isUIntPatLit? (v : Expr) : Option (Name × Expr) :=
  match v with
  | Expr.app (Expr.const (Name.str typeName "mk" ..) ..) val .. =>
    if isUIntTypeName typeName && isFinPatLit val then
      some (typeName, val.appArg!)
    else
      none
  | _ => none

def isUIntPatLit (v : Expr) : Bool :=
  isUIntPatLit? v |>.isSome

/--
  The frontend expands uint numerals occurring in patterns into `UInt*.mk ..` constructor applications.
  This method convert them back into `UInt*.ofNat ..` applications.
-/
def foldPatValue (v : Expr) : Expr :=
  match isUIntPatLit? v with
  | some (typeName, numLit) => mkApp (mkConst (Name.mkStr typeName "ofNat")) numLit
  | _ => v


/-- Return true is `e` is a term that should be processed by the `match`-compiler using `casesValues` -/
def isMatchValue (e : Expr) : Bool :=
  e.isNatLit || e.isCharLit || e.isStringLit || isFinPatLit e || isUIntPatLit e

end Lean.Meta
