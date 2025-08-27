/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.AC
public import Lean.Meta.Tactic.Grind.VarRename
namespace Lean.Grind.AC
open Lean.Meta.Grind

public def Seq.renameVars (s : Seq) (f : VarRename) : Seq :=
  match s with
  | .var x    => .var (f x)
  | .cons x s => .cons (f x) (renameVars s f)

public def Expr.renameVars (e : Expr) (f : VarRename) : Expr :=
  match e with
  | .var x => .var (f x)
  | .op a b => .op (renameVars a f) (renameVars b f)

public def Seq.collectVars (s : Seq) : VarCollector :=
  match s with
  | .var x => collectVar x
  | .cons x s => collectVar x >> s.collectVars

public def Expr.collectVars (e : Expr) : VarCollector :=
  match e with
  | .var x => collectVar x
  | .op a b  => a.collectVars >> b.collectVars

end Lean.Grind.AC
