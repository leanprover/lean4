/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.DependsOn
import Lean.Compiler.LCNF.PassManager

namespace Lean.Compiler.LCNF
namespace PullFunDecls

/--
Local function declaration and join point being pulled.
-/
structure ToPull where
  isFun : Bool
  decl  : FunDecl
  used  : FVarIdSet
  deriving Inhabited

/--
The `PullM` state contains the local function declarations and join points being pulled.
-/
abbrev PullM := StateRefT (List ToPull) CompilerM

/--
Extract from the state any local function declarations that depends on the given
free variable. The idea is that we have to stop pulling these declarations because they
depend on `fvarId`.
-/
def findFVarDirectDeps (fvarId : FVarId) : PullM (List ToPull) := do
  let s ← get
  unless s.any fun info => info.used.contains fvarId do
    return []
  let (s₁, s₂) ←  go s [] []
  set s₁
  return s₂
where
  go (as keep dep : List ToPull) : CoreM (List ToPull × List ToPull) := do
    match as with
    | [] => return (keep, dep)
    | a :: as =>
      if a.used.contains fvarId then
        go as keep (a :: dep)
      else
        go as (a :: keep) dep

partial def findFVarDepsFixpoint (todo : List ToPull) (acc : Array ToPull := #[]) : PullM (Array ToPull) := do
  match todo with
  | [] => return acc
  | p :: ps =>
    let psNew ← findFVarDirectDeps p.decl.fvarId
    findFVarDepsFixpoint (psNew ++ ps) (acc.push p)

partial def findFVarDeps (fvarId : FVarId) : PullM (Array ToPull) := do
  let ps ← findFVarDirectDeps fvarId
  findFVarDepsFixpoint ps

/--
Similar to `findFVarDeps`. Extract from the state any local function declarations that depends on the given
parameters.
-/
def findParamsDeps (params : Array Param) : PullM (Array ToPull) := do
  let mut acc := #[]
  for param in params do
    acc := acc ++ (← findFVarDeps param.fvarId)
  return acc

/--
Construct the code `fun p.decl k` or `jp p.decl k`.
-/
def ToPull.attach (p : ToPull) (k : Code) : Code :=
  if p.isFun then
    .fun p.decl k
  else
    .jp p.decl k

/--
Attach the given array of local function declarations and join points to `k`.
-/
partial def attach (ps : Array ToPull) (k : Code) : Code := Id.run do
  let visited := ps.map fun _ => false
  let (_, (k, _)) := go |>.run (k, visited)
  return k
where
  go : StateM (Code × Array Bool) Unit := do
    for i in [:ps.size] do
      visit i

  visited (i : Nat) : StateM (Code × Array Bool) Bool :=
    return (← get).2[i]!

  visit (i : Nat) : StateM (Code × Array Bool) Unit := do
    unless (← visited i) do
      modify fun (k, visited) => (k, visited.set! i true)
      let pi := ps[i]!
      for h : j in [:ps.size] do
        unless (← visited j) do
          let pj := ps[j]
          if pj.used.contains pi.decl.fvarId then
            visit j
      modify fun (k, visited) => (pi.attach k, visited)

/--
Extract from the state any local function declarations that depends on the given
free variable, **and** attach to code `k`.
-/
partial def attachFVarDeps (fvarId : FVarId) (k : Code) : PullM Code := do
  let ps ← findFVarDeps fvarId
  return attach ps k

/--
Similar to `attachFVarDeps`. Extract from the state any local function declarations that depends on the given
parameters, **and** attach to code `k`.
-/
def attachParamsDeps (params : Array Param) (k : Code) : PullM Code := do
  let ps ← findParamsDeps params
  return attach ps k

def attachJps (k : Code) : PullM Code := do
  let jps := (← get).filter fun info => !info.isFun
  modify fun s => s.filter fun info => info.isFun
  let jps ← findFVarDepsFixpoint jps
  return attach jps k

mutual
/--
Add local function declaration (or join point if `isFun = false`) to the state.
-/
partial def addToPull (isFun : Bool) (decl : FunDecl) : PullM Unit := do
  let saved ← get
  modify fun _ => []
  let mut value ← pull decl.value
  value ← attachParamsDeps decl.params value
  if isFun then
    /- Recall that a local function declaration cannot jump to join points defined out of its scope. -/
    value ← attachJps value
  let decl ← decl.update' decl.type value
  modify fun s => { isFun, decl, used := decl.collectUsed } :: s ++ saved

/--
Pull local function declarations and join points in `code`.
The state contains the declarations being pulled.
-/
partial def pull (code : Code) : PullM Code := do
  match code with
  | .let decl k =>
    let k ← pull k
    let k ← attachFVarDeps decl.fvarId k
    return code.updateLet! decl k
  | .fun decl k => addToPull true decl; pull k
  | .jp decl k => addToPull false decl; pull k
  | .cases c =>
    let alts ← c.alts.mapMonoM fun alt => do
      match alt with
      | .default k => return alt.updateCode (← pull k)
      | .alt _ ps k =>
        let k ← pull k
        let k ← attachParamsDeps ps k
        return alt.updateCode k
    return code.updateAlts! alts
  | .return .. | .unreach .. | .jmp .. => return code

end
end PullFunDecls

open PullFunDecls

/--
Pull local function declarations and join points in the given declaration.
-/
def Decl.pullFunDecls (decl : Decl) : CompilerM Decl := do
  let (value, ps) ← pull decl.value |>.run []
  let value := attach ps.toArray value
  return { decl with value }

def pullFunDecls : Pass :=
  .mkPerDeclaration `pullFunDecls Decl.pullFunDecls .base

builtin_initialize
  registerTraceClass `Compiler.pullFunDecls (inherited := true)

namespace Lean.Compiler.LCNF
