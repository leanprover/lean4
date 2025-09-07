/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Ring.Poly
public import Init.Grind.Ring.OfSemiring
public import Lean.Meta.Tactic.Grind.VarRename
namespace Lean.Grind.CommRing
open Lean.Meta.Grind

public def Power.renameVars (pw : Power) (f : VarRename) : Power :=
  { pw with x := (f pw.x) }

public def Mon.renameVars (m : Mon) (f : VarRename) : Mon :=
  match m with
  | .unit => .unit
  | .mult pw m => .mult (pw.renameVars f) (renameVars m f)

public def Poly.renameVars (p : Poly) (f : VarRename) : Poly :=
  match p with
  | .num _ => p
  | .add k m p => .add k (m.renameVars f) (renameVars p f)

public def Expr.renameVars (e : Expr) (f : VarRename) : Expr :=
  match e with
  | .num .. | .natCast .. | .intCast .. => e
  | .var x => .var (f x)
  | .neg a => .neg (renameVars a f)
  | .add a b => .add (renameVars a f) (renameVars b f)
  | .sub a b => .sub (renameVars a f) (renameVars b f)
  | .mul a b => .mul (renameVars a f) (renameVars b f)
  | .pow a k => .pow (renameVars a f) k

public def Power.collectVars (pw : Power) : VarCollector :=
  collectVar pw.x

public def Mon.collectVars (m : Mon) : VarCollector :=
  match m with
  | .unit => id
  | .mult pw m => pw.collectVars >> m.collectVars

public def Poly.collectVars (p : Poly) : VarCollector :=
  match p with
  | .num _ => id
  | .add _ m p => m.collectVars >> p.collectVars

public def Expr.collectVars (e : Expr) : VarCollector :=
  match e with
  | .num .. | .natCast .. | .intCast .. => id
  | .var x => collectVar x
  | .neg a | .pow a _ => a.collectVars
  | .add a b | .sub a b | .mul a b => a.collectVars >> b.collectVars

end Lean.Grind.CommRing

namespace Lean.Grind.Ring.OfSemiring
open Lean.Meta.Grind

public def Expr.renameVars (e : Expr) (f : VarRename) : Expr :=
  match e with
  | .num .. => e
  | .var x => .var (f x)
  | .add a b => .add (renameVars a f) (renameVars b f)
  | .mul a b => .mul (renameVars a f) (renameVars b f)
  | .pow a k => .pow (renameVars a f) k

public def Expr.collectVars (e : Expr) : VarCollector :=
  match e with
  | .num .. => id
  | .var x => collectVar x
  | .pow a _ => a.collectVars
  | .add a b | .mul a b => a.collectVars >> b.collectVars

end Lean.Grind.Ring.OfSemiring
