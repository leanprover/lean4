/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Expr
import Init.Grind.Ring.Envelope
import Init.Grind.Module.Envelope
namespace Lean.Meta.Grind

/-- Returns `true` if `declName` is the name of a cast-like function used to implement `grind` solvers -/
public def isCastLikeDeclName (declName : Name) : Bool :=
  declName == ``Grind.Ring.OfSemiring.toQ ||
  declName == ``Grind.IntModule.OfNatModule.toQ ||
  declName == ``Grind.ToInt.toInt ||
  declName == ``NatCast.natCast ||
  declName == ``IntCast.intCast

/-- Returns `true` if `f` is a cast-like operation. -/
public def isCastLikeFn (f : Expr) : Bool := Id.run do
  let .const declName _ := f | return false
  return isCastLikeDeclName declName

public def isCastLikeApp (e : Expr) : Bool :=
  isCastLikeFn e.getAppFn

end Lean.Meta.Grind
