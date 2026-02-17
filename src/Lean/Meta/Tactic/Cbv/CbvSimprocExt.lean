/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module
prelude
public import Lean.ScopedEnvExtension
public import Lean.Meta.Sym.Simp.Simproc
public import Lean.Meta.Sym.Simp.DiscrTree
public import Lean.Meta.DiscrTree.Basic

public section
namespace Lean.Meta.Tactic.Cbv
open Lean.Meta.Sym.Simp
open Lean.Meta.Sym
open DiscrTree

/--
Serializable entry for cbv simproc extension (stored in .olean, no function pointer).
-/
structure CbvSimprocDecl where
  declName : Name
  post     : Bool := true
  keys     : Array Key
  deriving Inhabited

/--
Runtime entry for cbv simproc (includes the actual function).
-/
structure CbvSimprocEntry where
  declName : Name
  proc     : Simproc

instance : BEq CbvSimprocEntry where
  beq e₁ e₂ := e₁.declName == e₂.declName

/--
State for cbv simproc extension: separate discrimination trees for pre and post simprocs.
-/
structure CbvSimprocState where
  pre  : DiscrTree CbvSimprocEntry := {}
  post : DiscrTree CbvSimprocEntry := {}
  deriving Inhabited

def CbvSimprocState.insert (s : CbvSimprocState) (post : Bool) (keys : Array Key) (entry : CbvSimprocEntry) : CbvSimprocState :=
  if post then
    { s with post := s.post.insertKeyValue keys entry }
  else
    { s with pre := s.pre.insertKeyValue keys entry }

/-- Global ref for builtin cbv simproc declarations (keys + post flag, populated during initialization). -/
builtin_initialize builtinCbvSimprocDeclsRef : IO.Ref (Std.HashMap Name (Bool × Array Key)) ← IO.mkRef {}

/-- Global ref for builtin cbv simprocs (runtime state with actual functions). -/
builtin_initialize builtinCbvSimprocsRef : IO.Ref CbvSimprocState ← IO.mkRef {}

/--
Register a builtin cbv simproc. Called during `builtin_initialize`.
-/
def registerBuiltinCbvSimproc (declName : Name) (post : Bool) (keys : Array Key) (proc : Simproc) : IO Unit := do
  unless (← initializing) do
    throw (IO.userError s!"Invalid builtin cbv simproc declaration: It can only be registered during initialization")
  if (← builtinCbvSimprocDeclsRef.get).contains declName then
    throw (IO.userError s!"Invalid builtin cbv simproc declaration `{privateToUserName declName}`: already declared")
  builtinCbvSimprocDeclsRef.modify fun m => m.insert declName (post, keys)
  builtinCbvSimprocsRef.modify fun s => s.insert post keys { declName, proc }

abbrev CbvSimprocExtension := SimpleScopedEnvExtension CbvSimprocDecl CbvSimprocState

unsafe def getCbvSimprocFromDeclImpl (declName : Name) : ImportM Simproc := do
  let ctx ← read
  match ctx.env.find? declName with
  | none => throw <| IO.userError s!"Unknown constant `{declName}`"
  | some info =>
    match info.type with
    | .const ``Lean.Meta.Sym.Simp.Simproc _ =>
      IO.ofExcept <| ctx.env.evalConst Simproc ctx.opts declName
    | _ => throw <| IO.userError s!"Cbv simproc `{privateToUserName declName}` has unexpected type: Expected `Simproc`, found `{info.type}`"

@[implemented_by getCbvSimprocFromDeclImpl]
opaque getCbvSimprocFromDecl (declName : Name) : ImportM Simproc

builtin_initialize cbvSimprocExt : CbvSimprocExtension ←
  registerSimpleScopedEnvExtension {
    name     := `cbvSimprocExt
    initial  := {}
    addEntry := fun s e =>
      s.insert e.post e.keys { declName := e.declName, proc := fun _ => return .rfl }
    exportEntry? := fun level entry => do
      guard (level == .private || !isPrivateName entry.declName)
      return entry
  }

/--
Look up all cbv pre-simprocs matching expression `e`.
-/
def getCbvPreSimprocs (e : Expr) : CoreM (Array CbvSimprocEntry) := do
  let builtinState ← builtinCbvSimprocsRef.get
  let builtinMatches := Sym.getMatch builtinState.pre e
  let extState := cbvSimprocExt.getState (← getEnv)
  let userMatches := Sym.getMatch extState.pre e
  let mut result := builtinMatches
  for entry in userMatches do
    let proc ← getCbvSimprocFromDecl entry.declName
    result := result.push { declName := entry.declName, proc }
  return result

/--
Look up all cbv post-simprocs matching expression `e`.
-/
def getCbvPostSimprocs (e : Expr) : CoreM (Array CbvSimprocEntry) := do
  let builtinState ← builtinCbvSimprocsRef.get
  let builtinMatches := Sym.getMatch builtinState.post e
  let extState := cbvSimprocExt.getState (← getEnv)
  let userMatches := Sym.getMatch extState.post e
  let mut result := builtinMatches
  for entry in userMatches do
    let proc ← getCbvSimprocFromDecl entry.declName
    result := result.push { declName := entry.declName, proc }
  return result

end Lean.Meta.Tactic.Cbv
