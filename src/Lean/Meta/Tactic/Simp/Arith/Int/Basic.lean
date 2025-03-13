/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Int.Linear
import Lean.Util.SortExprs
import Lean.Meta.Check
import Lean.Meta.Offset
import Lean.Meta.IntInstTesters
import Lean.Meta.AppBuilder
import Lean.Meta.KExprMap
import Lean.Data.RArray

namespace Int.Linear

/-- Converts the linear polynomial into the "simplified" expression -/
def Poly.toExpr (p : Poly) : Expr :=
  go none p
where
  go : Option Expr → Poly → Expr
    | none,   .num k     => .num k
    | some e, .num 0     => e
    | some e, .num k     => .add e (.num k)
    | none,   .add 1 x p => go (some (.var x)) p
    | none,   .add k x p => go (some (.mulL k (.var x))) p
    | some e, .add 1 x p => go (some (.add e (.var x))) p
    | some e, .add k x p => go (some (.add e (.mulL k (.var x)))) p

/-- Applies the given variable permutation to `e` -/
def Expr.applyPerm (perm : Lean.Perm) (e : Expr) : Expr :=
  go e
where
  go : Expr → Expr
    | .num v    => .num v
    | .var i    => .var (perm[(i : Nat)]?.getD i)
    | .neg a    => .neg (go a)
    | .add a b  => .add (go a) (go b)
    | .sub a b  => .sub (go a) (go b)
    | .mulL k a => .mulL k (go a)
    | .mulR a k => .mulR (go a) k

deriving instance Repr for Poly
deriving instance Repr for Expr

end Int.Linear

namespace Lean.Meta.Simp.Arith.Int

def ofPoly (p : Int.Linear.Poly) : Expr :=
  open Int.Linear.Poly in
  match p with
  | .num v => mkApp (mkConst ``num) (toExpr v)
  | .add k v p => mkApp3 (mkConst ``add) (toExpr k) (toExpr v) (ofPoly p)

instance : ToExpr Int.Linear.Poly where
  toExpr a := ofPoly a
  toTypeExpr := mkConst ``Int.Linear.Poly

def ofLinearExpr (e : Int.Linear.Expr) : Expr :=
  open Int.Linear.Expr in
  match e with
  | .num v    => mkApp (mkConst ``num) (toExpr v)
  | .var i    => mkApp (mkConst ``var) (mkNatLit i)
  | .neg a    => mkApp (mkConst ``neg) (ofLinearExpr a)
  | .add a b  => mkApp2 (mkConst ``add) (ofLinearExpr a) (ofLinearExpr b)
  | .sub a b  => mkApp2 (mkConst ``sub) (ofLinearExpr a) (ofLinearExpr b)
  | .mulL k a => mkApp2 (mkConst ``mulL) (toExpr k) (ofLinearExpr a)
  | .mulR a k => mkApp2 (mkConst ``mulR) (ofLinearExpr a) (toExpr k)

instance : ToExpr Int.Linear.Expr where
  toExpr a := ofLinearExpr a
  toTypeExpr := mkConst ``Int.Linear.Expr

def _root_.Int.Linear.Expr.denoteExpr (ctx : Nat → Expr) (e : Int.Linear.Expr) : MetaM Expr := do
  match e with
  | .num v    => return Lean.toExpr v
  | .var x    => return ctx x
  | .neg a    => return mkIntNeg (← denoteExpr ctx a)
  | .add a b  => return mkIntAdd (← denoteExpr ctx a) (← denoteExpr ctx b)
  | .sub a b  => return mkIntSub (← denoteExpr ctx a) (← denoteExpr ctx b)
  | .mulL k a => return mkIntMul (toExpr k) (← denoteExpr ctx a)
  | .mulR a k => return mkIntMul (← denoteExpr ctx a) (toExpr k)

def _root_.Int.Linear.Poly.denoteExpr (ctx : Nat → Expr) (p : Int.Linear.Poly) : MetaM Expr := do
  match p with
  | .num k => return toExpr k
  | .add 1 x p => go (ctx x) p
  | .add k x p => go (mkIntMul (toExpr k) (ctx x)) p
where
  go (r : Expr)  (p : Int.Linear.Poly) : MetaM Expr :=
    match p with
    | .num 0 => return r
    | .num k => return mkIntAdd r (toExpr k)
    | .add 1 x p => go (mkIntAdd r (ctx x)) p
    | .add k x p => go (mkIntAdd r (mkIntMul (toExpr k) (ctx x))) p

namespace ToLinear

structure State where
  varMap : KExprMap Nat := {} -- It should be fine to use `KExprMap` here because the mapping should be small and few HeadIndex collisions.
  vars   : Array Expr := #[]

abbrev M := StateRefT State MetaM

open Int.Linear.Expr

def addAsVar (e : Expr) : M Int.Linear.Expr := do
  if let some x ← (← get).varMap.find? e then
    return var x
  else
    let x := (← get).vars.size
    let s ← get
    set { varMap := (← s.varMap.insert e x), vars := s.vars.push e : State }
    return var x

partial def toLinearExpr (e : Expr) : M Int.Linear.Expr := do
  match e with
  | .mdata _ e            => toLinearExpr e
  | .app ..               => visit e
  | .mvar ..              => visit e
  | _                     => addAsVar e
where
  visit (e : Expr) : M Int.Linear.Expr := do
    let mul (a b : Expr) := do
      match (← getIntValue? a) with
      | some k => return .mulL k (← toLinearExpr b)
      | none => match (← getIntValue? b) with
        | some k => return .mulR (← toLinearExpr a) k
        | none => addAsVar e
    match_expr e with
    | OfNat.ofNat _ _ _ =>
      if let some n ← getIntValue? e then return .num n
      else addAsVar e
    | Int.neg a => return .neg (← toLinearExpr a)
    | Neg.neg _ i a =>
      if (← isInstNegInt i) then return .neg (← toLinearExpr a)
      else addAsVar e
    | Int.add a b => return .add (← toLinearExpr a) (← toLinearExpr b)
    | Add.add _ i a b =>
      if (← isInstAddInt i) then return .add (← toLinearExpr a) (← toLinearExpr b)
      else addAsVar e
    | HAdd.hAdd _ _ _ i a b =>
      if (← isInstHAddInt i) then return .add (← toLinearExpr a) (← toLinearExpr b)
      else addAsVar e
    | Int.sub a b => return .sub (← toLinearExpr a) (← toLinearExpr b)
    | Sub.sub _ i a b =>
      if (← isInstSubInt i) then return .sub (← toLinearExpr a) (← toLinearExpr b)
      else addAsVar e
    | HSub.hSub _ _ _ i a b =>
      if (← isInstHSubInt i) then return .sub (← toLinearExpr a) (← toLinearExpr b)
      else addAsVar e
    | Int.mul a b => mul a b
    | Mul.mul _ i a b =>
      if (← isInstMulInt i) then mul a b
      else addAsVar e
    | HMul.hMul _ _ _ i a b =>
      if (← isInstHMulInt i) then mul a b
      else addAsVar e
    | _ => addAsVar e

partial def eqCnstr? (e : Expr) : M (Option (Int.Linear.Expr × Int.Linear.Expr)) := OptionT.run do
  let_expr Eq α a b ← e | failure
  let_expr Int ← α | failure
  let a ← toLinearExpr a
  let b ← toLinearExpr b
  match a, b with
  /-
  We do not want to convert `x = y` into `x + -1*y = 0`.
  Similarly, we don't want to convert `x = 3` into `x + -3 = 0`.
  `grind` and other tactics have better support for this kind of equalities.
  -/
  | .var _, .var _ | .var _, .num _ | .num _, .var _ => failure
  | _, _ => return (a, b)

partial def leCnstr? (e : Expr) : M (Option (Int.Linear.Expr × Int.Linear.Expr)) := OptionT.run do
  match_expr e with
  | Int.le a b =>
    return (← toLinearExpr a, ← toLinearExpr b)
  | Int.lt a b =>
    return (.add (← toLinearExpr a) (.num 1), ← toLinearExpr b)
  | LE.le _ i a b =>
    guard (← isInstLEInt i)
    return (← toLinearExpr a, ← toLinearExpr b)
  | LT.lt _ i a b =>
    guard (← isInstLTInt i)
    return (.add (← toLinearExpr a) (.num 1), ← toLinearExpr b)
  | GE.ge _ i a b =>
    guard (← isInstLEInt i)
    return (← toLinearExpr b, ← toLinearExpr a)
  | GT.gt _ i a b =>
    guard (← isInstLTInt i)
    return (.add (← toLinearExpr b) (.num 1), ← toLinearExpr a)
  | _ => failure

partial def dvdCnstr? (e : Expr) : M (Option (Int × Int.Linear.Expr)) := OptionT.run do
  let_expr Dvd.dvd _ inst k b ← e | failure
  guard (← isInstDvdInt inst)
  let some k ← getIntValue? k | failure
  return (k, ← toLinearExpr b)

def run (x : M α) : MetaM (α × Array Expr) := do
  let (a, s) ← x.run {}
  return (a, s.vars)

end ToLinear

def toLinearExpr (e : Expr) : MetaM (Int.Linear.Expr × Array Expr) := do
  let (e, atoms) ← ToLinear.run (ToLinear.toLinearExpr e)
  if atoms.size == 1 then
    return (e, atoms)
  else
    let (atoms, perm) := sortExprs atoms
    let e := e.applyPerm perm
    return (e, atoms)

@[inline]
private def adapter (e : Expr) (k : Expr → ToLinear.M (Option (Int.Linear.Expr × Int.Linear.Expr))) : MetaM (Option (Int.Linear.Expr × Int.Linear.Expr × Array Expr)) := do
  let (some (lhs, rhs), atoms) ← ToLinear.run (k e)
    | return none
  if atoms.size <= 1 then
    return some (lhs, rhs, atoms)
  else
    -- We use `lt := false` because `Poly.norm` sorts variables in decreasing order.
    -- It does that because of the cutsat procedure.
    let (atoms, perm) := sortExprs atoms (lt := false)
    let lhs := lhs.applyPerm perm
    let rhs := rhs.applyPerm perm
    return some (lhs, rhs, atoms)

def eqCnstr? (e : Expr) : MetaM (Option (Int.Linear.Expr × Int.Linear.Expr × Array Expr)) := do
  adapter e ToLinear.eqCnstr?

def leCnstr? (e : Expr) : MetaM (Option (Int.Linear.Expr × Int.Linear.Expr × Array Expr)) := do
  adapter e ToLinear.leCnstr?

def dvdCnstr? (e : Expr) : MetaM (Option (Int × Int.Linear.Expr × Array Expr)) := do
  let (some (d, e), atoms) ← ToLinear.run (ToLinear.dvdCnstr? e)
    | return none
  if atoms.size <= 1 then
    return some (d, e, atoms)
  else
    let (atoms, perm) := sortExprs atoms (lt := false)
    let e := e.applyPerm perm
    return some (d, e, atoms)

def toContextExpr (ctx : Array Expr) : Expr :=
  if h : 0 < ctx.size then
    RArray.toExpr (mkConst ``Int) id (RArray.ofArray ctx h)
  else
    RArray.toExpr (mkConst ``Int) id (RArray.leaf (mkIntLit 0))

end Lean.Meta.Simp.Arith.Int
