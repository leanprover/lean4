/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Lean.Meta.Sym.SymM

/-!
This module implements a generic visitor function for inspecting the atoms of EPR problems that are
already encoded into `Bool` and `BitVec` and in `bv_normalize` normal form, together with polarity
information.
-/

namespace Lean.Meta.Tactic.BVDecide.EPR

namespace BoolPolarityVisitor

variable {m : Type → Type} [Monad m] {σ : Type} [STWorld σ m] [MonadLiftT (ST σ) m]

structure State where
  cache : Std.HashSet (Expr × Bool) := {}

abbrev VisitM (m : Type → Type) {σ : Type} [STWorld σ m] := StateRefT State m

@[inline]
def withCheckCache (e : Expr) (polarity : Bool) (x : VisitM m Unit) : VisitM m Unit := do
  if (← get).cache.contains (e, polarity) then
    return ()
  else
    modify fun s => { s with cache := s.cache.insert (e, polarity) }
    x

@[specialize]
partial def visitBool' (e : Expr) (polarity : Bool) (f : Expr → Bool → m Unit) : VisitM m Unit := do
  withCheckCache e polarity do
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
    | Bool.xor p q => visitBothPolarities p q
    | BEq.beq α _ p q =>
      if α.isConstOf ``Bool then visitBothPolarities p q else f e polarity
    | cond α c p q =>
      if α.isConstOf ``Bool then
        visitBool' c true f
        visitBool' c false f
        visitBool' p polarity f
        visitBool' q polarity f
      else
        f e polarity
    | _ => f e polarity
where
  visitBothPolarities (p q : Expr) : VisitM m Unit := do
    visitBool' p true f
    visitBool' p false f
    visitBool' q true f
    visitBool' q false f

/--
Calls `f` at every atom of the `Bool` expression `e`, together with polarity information about that
atom. `e` is expected to be in `bv_normalize` normal form. The function does not visit the same
`(atom, pol)` pair twice even if it occurs twice in the problem.
-/
@[specialize]
public def visitBool (e : Expr) (f : Expr → Bool → m Unit) : m Unit :=
  StateRefT'.run' (visitBool' e true f) {}

end BoolPolarityVisitor

end Lean.Meta.Tactic.BVDecide.EPR
