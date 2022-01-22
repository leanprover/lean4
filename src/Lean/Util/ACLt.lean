/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr

namespace Lean

def Expr.ctorWeight : Expr → UInt8
  | bvar ..    => 0
  | fvar ..    => 1
  | mvar ..    => 2
  | sort ..    => 3
  | const ..   => 4
  | lit ..     => 5
  | mdata ..   => 6
  | proj ..    => 7
  | app ..     => 8
  | lam ..     => 9
  | forallE .. => 10
  | letE ..    => 11

namespace ACLt

mutual

/--
  An AC-compatible ordering.

  Recall that an AC-compatible ordering if it is monotonic, well-founded, and total.
  Both KBO and LPO are AC-compatible. KBO is faster, but we do not cache the weight of
  each expression in Lean 4, only the approximated depth (it saturates at 255).
  Thus, we use a hybrid of KBO and LPO.
-/
unsafe def lt (a b : Expr) : Bool :=
  if ptrAddrUnsafe a == ptrAddrUnsafe b then
    false
  -- We ignore metadata
  else if a.isMData then
    lt a.mdataExpr! b
  else if b.isMData then
    lt a b.mdataExpr!
  else if a.approxDepth < b.approxDepth then
    true
  else if a.approxDepth > b.approxDepth then
    false
  else if a.approxDepth < 255 then
    lex a b
  else
    lpo a b
where
  ltPair (a₁ a₂ b₁ b₂ : Expr) : Bool :=
    if a₁ != b₁ then lt a₁ b₁ else lt a₂ b₂

  lexSameCtor (a b : Expr) : Bool :=
    match a with
    -- Atomic
    | Expr.bvar i ..    => i < b.bvarIdx!
    | Expr.fvar id ..   => Name.quickLt id.name b.fvarId!.name
    | Expr.mvar id ..   => Name.quickLt id.name b.mvarId!.name
    | Expr.sort u ..    => Level.normLt u b.sortLevel!
    | Expr.const n ..   => Name.quickLt n b.constName! -- We igore the levels
    | Expr.lit v ..     => Literal.lt v b.litValue!
    -- Composite
    | Expr.proj _ i e ..    => if i != b.projIdx! then i < b.projIdx! else lt e b.projExpr!
    | Expr.app f e ..       => ltPair f e b.appFn! b.appArg!
    | Expr.lam _ d e ..     => ltPair d e b.bindingDomain! b.bindingBody!
    | Expr.forallE _ d e .. => ltPair d e b.bindingDomain! b.bindingBody!
    | Expr.letE _ _ v e ..  => ltPair v e b.letValue! b.letBody!
    -- See main function
    | Expr.mdata ..         => unreachable!

  lex (a b : Expr) : Bool :=
    if a.ctorWeight < b.ctorWeight then
      true
    else if a.ctorWeight > b.ctorWeight then
      false
    else
      lexSameCtor a b

  allChildrenLt (a b : Expr) : Bool :=
    match a with
    | Expr.proj _ _ e ..    => lt e b
    | Expr.app f e ..       => lt f b && lt e b
    | Expr.lam _ d e ..     => lt d b && lt e b
    | Expr.forallE _ d e .. => lt d b && lt e b
    | Expr.letE _ _ v e ..  => lt v b && lt e b
    | _ => unreachable!

  someChildGe (a b : Expr) : Bool :=
    !allChildrenLt a b

  -- lpo is only used when `a` and `b` have the same approximate depth, and it is >= 255
  lpo (a b : Expr) : Bool :=
    -- Case 1: `a < b` if for some child `b_i` of `b`, we have `b_i >= a`
    someChildGe b a
    -- Case 2: `a < b` if `a.ctorWeight < b.ctorWeight` and for all children `a_i` of `a`, `a_i < b`
    || (a.ctorWeight < b.ctorWeight && allChildrenLt a b)
    -- Case 3: `a < b` if `a` & `b` have the same ctor, and `a` is lexicographically smaller
    || (a.ctorWeight == b.ctorWeight && lexSameCtor a b)

end

end ACLt

@[implementedBy ACLt.lt]
constant Expr.acLt : Expr → Expr → Bool

end Lean
