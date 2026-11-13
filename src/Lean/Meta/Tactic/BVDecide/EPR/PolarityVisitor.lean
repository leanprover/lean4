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

mutual

/-
We special case these because bool facts frequently occur as `b = true`. In this situation we would
naively analyze `b` with both polarities, despite that not being necessary.
-/
@[specialize]
partial def visitBool'.visitBoth (p q : Expr) (polarity flip : Bool) (f : Expr → Bool → m Unit) :
    VisitM m Unit := do
  match_expr (meta := false) p with
  | Bool.true => visitBool' q (polarity ^^ flip) f
  | Bool.false => visitBool' q (!polarity ^^ flip) f
  | _ =>
    match_expr (meta := false) q with
    | Bool.true => visitBool' p (polarity ^^ flip) f
    | Bool.false => visitBool' p (!polarity ^^ flip) f
    | _ =>
      visitBool' p true f
      visitBool' p false f
      visitBool' q true f
      visitBool' q false f

@[specialize]
partial def visitProp'.visitBoth (p q : Expr) (polarity flip : Bool) (f : Expr → Bool → m Unit) :
    VisitM m Unit := do
  match_expr (meta := false) p with
  | True => visitProp' q (polarity ^^ flip) f
  | False => visitProp' q (!polarity ^^ flip) f
  | _ =>
    match_expr (meta := false) q with
    | True => visitProp' p (polarity ^^ flip) f
    | False => visitProp' p (!polarity ^^ flip) f
    | _ =>
      visitProp' p true f
      visitProp' p false f
      visitProp' q true f
      visitProp' q false f

@[specialize]
partial def visitBool' (e : Expr) (polarity : Bool) (f : Expr → Bool → m Unit) : VisitM m Unit := do
  VisitM.withCheckCache e polarity do
    match_expr (meta := false) e with
    | Bool.true => return ()
    | Bool.false => return ()
    | Bool.not p => visitBool' p (!polarity) f
    | Bool.and p q =>
      visitBool' p polarity f
      visitBool' q polarity f
    | Bool.or p q =>
      visitBool' p polarity f
      visitBool' q polarity f
    | Bool.xor p q => visitBool'.visitBoth p q polarity true f
    | BEq.beq α _ p q =>
      if α.isConstOf ``Bool then visitBool'.visitBoth p q polarity false f else f e polarity
    | cond _ c p q =>
      visitBool' c true f
      visitBool' c false f
      visitBool' p polarity f
      visitBool' q polarity f
    | ite _ c _ p q =>
      visitProp' c true f
      visitProp' c false f
      visitBool' p polarity f
      visitBool' q polarity f
    | decide p _ => visitProp' p polarity f
    | _ => f e polarity

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
      | Iff p q => visitProp'.visitBoth p q polarity false f
      | Eq α lhs rhs =>
        if α.isProp then
          visitProp'.visitBoth lhs rhs polarity false f
        else if α.isConstOf ``Bool then
          visitBool'.visitBoth lhs rhs polarity false f
        else
          f e polarity
      | cond _ c p q =>
        visitBool' c true f
        visitBool' c false f
        visitProp' p polarity f
        visitProp' q polarity f
      | ite _ c _ p q =>
        visitProp' c true f
        visitProp' c false f
        visitProp' p polarity f
        visitProp' q polarity f
      | _ => f e polarity

end

/--
Calls `f` at every atom of the EPR expression `e`, together with polarity information about that
atom. The function does not visit the same `(atom, pol)` pair twice even if it occurs twice in the
problem.
-/
@[specialize]
public def visitProp (e : Expr) (f : Expr → Bool → m Unit) : m Unit :=
  VisitM.run do
    visitProp' e true f

/--
Calls `f` at every atom of the `Bool` expression `e`, together with polarity information about that
atom. `e` is expected to be in `bv_normalize` normal form. The function does not visit the same
`(atom, pol)` pair twice even if it occurs twice in the problem.
-/
@[specialize]
public def visitBool (e : Expr) (f : Expr → Bool → m Unit) : m Unit :=
  StateRefT'.run' (visitBool' e true f) {}

end PolarityVisitor

end Lean.Meta.Tactic.BVDecide.EPR
