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

/--
Returns `true` if `declName` is the embedding into an envelope type created by a `grind` solver,
e.g., the ring solver embeds a commutative semiring into `Grind.Ring.OfSemiring.Q`.
-/
def isEnvelopeEmbeddingDeclName (declName : Name) : Bool :=
  declName == ``Grind.Ring.OfSemiring.toQ ||
  declName == ``Grind.IntModule.OfNatModule.toQ

/-- Returns `true` if `f` is the embedding into an envelope type created by a `grind` solver. -/
public def isEnvelopeEmbeddingFn (f : Expr) : Bool := Id.run do
  let .const declName _ := f | return false
  return isEnvelopeEmbeddingDeclName declName

/--
Returns `true` if `declName` is the name of a cast-like function used to implement `grind` solvers.
Unlike envelope embeddings, `NatCast.natCast` and `IntCast.intCast` also occur in user terms
and may target types that no solver interprets (e.g., `ZMod n`).
-/
public def isCastLikeDeclName (declName : Name) : Bool :=
  isEnvelopeEmbeddingDeclName declName ||
  declName == ``NatCast.natCast ||
  declName == ``IntCast.intCast
  -- TODO: add support for new `toInt` and `toNat`

/-- Returns `true` if `f` is a cast-like operation. -/
public def isCastLikeFn (f : Expr) : Bool := Id.run do
  let .const declName _ := f | return false
  return isCastLikeDeclName declName

public def isCastLikeApp (e : Expr) : Bool :=
  isCastLikeFn e.getAppFn

end Lean.Meta.Grind
