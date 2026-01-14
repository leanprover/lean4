/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.IR.CompilerM

public section

namespace Lean.IR
namespace Sorry

structure State where
  localSorryMap : NameMap Name := {}
  modified : Bool := false

abbrev M := StateT State CompilerM

def visitExpr : Expr → ExceptT Name M Unit
  | Expr.fap f _  => getSorryDepFor? f
  | Expr.pap f _  => getSorryDepFor? f
  | _             => return ()
where
  getSorryDepFor? (f : Name) : ExceptT Name M Unit := do
    let found (g : Name) :=
      if g == ``sorryAx then
        throwThe Name f
      else
        throwThe Name g
    if f == ``sorryAx then
      throwThe Name f
    else if let some g := (← get).localSorryMap.find? f then
      found g
    else match (← findDecl f) with
      | some (.fdecl (info := { sorryDep? := some g, .. }) ..) => found g
      | _ => return ()

partial def visitFnBody (b : FnBody) : ExceptT Name M Unit := do
  match b with
  | .vdecl _ _ v b   => visitExpr v; visitFnBody b
  | .jdecl _ _ v b   => visitFnBody v; visitFnBody b
  | .case _ _ _ alts => alts.forM fun alt => visitFnBody alt.body
  | _ =>
    unless b.isTerminal do
      visitFnBody b.body

def visitDecl (d : Decl) : M Unit := do
  match d with
  | .fdecl (f := f) (body := b) .. =>
    match (← get).localSorryMap.find? f with
    | some _ => return ()
    | none =>
      match (← visitFnBody b |>.run) with
      | .ok _    => return ()
      | .error g =>
        modify fun s => {
          localSorryMap := s.localSorryMap.insert f g
          modified      := true
        }
  | _ => return ()

partial def collect (decls : Array Decl) : M Unit := do
  modify fun s => { s with modified := false }
  decls.forM visitDecl
  if (← get).modified then
    collect decls

end Sorry

def updateSorryDep (decls : Array Decl) : CompilerM (Array Decl) := do
  let (_, s) ← Sorry.collect decls |>.run {}
  return decls.map fun decl =>
    match decl with
    | Decl.fdecl f xs t b _    =>
      match s.localSorryMap.find? f with
      | some g => Decl.fdecl f xs t b { sorryDep? := some g }
      | _ => decl
    | _ => decl

end Lean.IR
