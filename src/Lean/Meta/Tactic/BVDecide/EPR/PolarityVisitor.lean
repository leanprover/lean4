/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Lean.Meta.Tactic.BVDecide.EPR.Basic

/-!
This module implements a generic visitor function for inspecting the atoms of EPR problems together
with polarity information.
-/

namespace Lean.Meta.Tactic.BVDecide.EPR

variable {m : Type → Type} [Monad m] {σ : Type} [STWorld σ m] [MonadLiftT (ST σ) m]

structure VisitState where
  cache : Std.HashSet (Expr × Bool) := {}

abbrev VisitM (m : Type → Type) {σ : Type} [STWorld σ m] := StateRefT VisitState m

namespace VisitM

def run (x : VisitM m α) : m α :=
  StateRefT'.run' x {}

@[inline]
def withCheckCache (e : Expr) (polarity : Bool) (x : VisitM m Unit) : VisitM m Unit := do
  if (← get).cache.contains (e, polarity) then
    return ()
  else
    modify fun s => { s with cache := s.cache.insert (e, polarity) }
    x

end VisitM

namespace PolarityVisitor

@[specialize]
partial def visitProp' (e : Expr) (polarity : Bool) (f : Expr → Bool → m Unit) :
    VisitM m Unit := do
  VisitM.withCheckCache e polarity do
    match e with
    | .forallE _ dom body _ =>
      assert! !body.hasLooseBVar 0
      visitProp' dom (!polarity) f
      visitProp' body polarity f
    | _ =>
      match_expr (meta := false) e with
      | Not p => visitProp' p (!polarity) f
      | And p q =>
        visitProp' p polarity f
        visitProp' q polarity f
      | Or p q =>
        visitProp' p polarity f
        visitProp' q polarity f
      | Iff p q =>
        visitProp' p true f
        visitProp' p false f
        visitProp' q true f
        visitProp' q false f
      | Eq α lhs rhs =>
        if α.isProp then
          visitProp' lhs true f
          visitProp' lhs false f
          visitProp' rhs true f
          visitProp' rhs false f
        else
          f e polarity
      | _ => f e polarity


/--
Calls `f` at every atom of the EPR expression `e`, together with polarity information about that
atom. The function does not visit the same `(atom, pol)` pair twice even if it occurs twice in the
problem.
-/
@[specialize]
public def visitProp (e : Expr) (f : Expr → Bool → m Unit) : m Unit :=
  VisitM.run do
    visitProp' e true f

end PolarityVisitor

end Lean.Meta.Tactic.BVDecide.EPR
