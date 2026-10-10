/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Robin Arnez
-/
module

prelude
public import Lean.Compiler.Bytecode.Basic

public section

namespace Lean.Compiler.Bytecode
namespace Sorry

structure State where
  localSorryMap : NameMap Name := {}
  modified : Bool := false

abbrev M := ReaderT Environment <| StateM State

def getSorryDepFor? (f : Name) : ExceptT Name M Unit := do
  let found (g : Name) :=
    if g == ``sorryAx then
      throwThe Name f
    else
      throwThe Name g
  if f == ``sorryAx then
    throwThe Name f
  else if let some g := (← get).localSorryMap.find? f then
    found g
  else match findBytecodeDecl (← read) f with
    | some { sorryDep? := some g, .. } => found g
    | _ => return ()

def visitDecl (d : BytecodeDecl) : M Unit := do
  if (← get).localSorryMap.contains d.name then
    return
  let res ← (d.symbols.forM getSorryDepFor?).run
  match res with
  | .ok _    => return ()
  | .error g =>
    modify fun s => {
      localSorryMap := s.localSorryMap.insert d.name g
      modified      := true
    }

partial def collect (decls : Array BytecodeDecl) : M Unit := do
  modify fun s => { s with modified := false }
  decls.forM visitDecl
  if (← get).modified then
    collect decls

end Sorry

def updateSorryDep (decls : Array BytecodeDecl) : CoreM (Array BytecodeDecl) := do
  let (_, s) ← Sorry.collect decls |>.run (← getEnv) |>.run {}
  return decls.map fun decl =>
    match s.localSorryMap.find? decl.name with
    | some g => { decl with sorryDep? := g }
    | _ => decl

end Lean.Compiler.Bytecode
