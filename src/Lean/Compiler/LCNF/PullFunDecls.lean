/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.LCNF.DependsOn
public import Lean.Compiler.LCNF.PassManager

public section

namespace Lean.Compiler.LCNF
namespace PullFunDecls

/--
Local function declaration and join point being pulled.
-/
structure ToPull (ph : IRPhase) where
  isFun : Bool
  decl  : FunDecl ph
  used  : FVarIdHashSet
  deriving Inhabited

/--
The `PullM` state contains the local function declarations and join points being pulled.
-/
abbrev PullM (ph : IRPhase) := StateRefT (List (ToPull ph)) CompilerM

/--
Extract from the state any local function declarations that depends on the given
free variable. The idea is that we have to stop pulling these declarations because they
depend on `fvarId`.
-/
def findFVarDirectDeps (fvarId : FVarId) : PullM ph (List (ToPull ph)) := do
  let s ← get
  unless s.any fun info => info.used.contains fvarId do
    return []
  let (s₁, s₂) ←  go s [] []
  set s₁
  return s₂
where
  go (as keep dep : List (ToPull ph)) : CoreM (List (ToPull ph) × List (ToPull ph)) := do
    match as with
    | [] => return (keep, dep)
    | a :: as =>
      if a.used.contains fvarId then
        go as keep (a :: dep)
      else
        go as (a :: keep) dep

partial def findFVarDepsFixpoint (todo : List (ToPull ph)) (acc : Array (ToPull ph) := #[]) :
    PullM ph (Array (ToPull ph)) := do
  match todo with
  | [] => return acc
  | p :: ps =>
    let psNew ← findFVarDirectDeps p.decl.fvarId
    findFVarDepsFixpoint (psNew ++ ps) (acc.push p)

partial def findFVarDeps (fvarId : FVarId) : PullM ph (Array (ToPull ph)) := do
  let ps ← findFVarDirectDeps fvarId
  findFVarDepsFixpoint ps

/--
Similar to `findFVarDeps`. Extract from the state any local function declarations that depends on the given
parameters.
-/
def findParamsDeps (params : Array (Param ph)) : PullM ph (Array (ToPull ph)) := do
  let mut acc := #[]
  for param in params do
    acc := acc ++ (← findFVarDeps param.fvarId)
  return acc

/--
Construct the code `fun p.decl k` or `jp p.decl k`.
-/
def ToPull.attach (p : ToPull ph) (k : Code ph) : Code ph :=
  if p.isFun then
    ph.withAssertPhase! .pure fun h =>
      .fun p.decl k h
  else
    .jp p.decl k

/--
Attach the given array of local function declarations and join points to `k`.
-/
partial def attach (ps : Array (ToPull ph)) (k : Code ph) : Code ph := Id.run do
  let visited := ps.map fun _ => false
  let (_, (k, _)) := go |>.run (k, visited)
  return k
where
  go : StateM (Code ph × Array Bool) Unit := do
    for i in *...ps.size do
      visit i

  visited (i : Nat) : StateM (Code ph × Array Bool) Bool :=
    return (← get).2[i]!

  visit (i : Nat) : StateM (Code ph × Array Bool) Unit := do
    unless (← visited i) do
      modify fun (k, visited) => (k, visited.set! i true)
      let pi := ps[i]!
      for h : j in *...ps.size do
        unless (← visited j) do
          let pj := ps[j]
          if pj.used.contains pi.decl.fvarId then
            visit j
      modify fun (k, visited) => (pi.attach k, visited)

/--
Extract from the state any local function declarations that depends on the given
free variable, **and** attach to code `k`.
-/
partial def attachFVarDeps (fvarId : FVarId) (k : Code ph) : PullM ph (Code ph) := do
  let ps ← findFVarDeps fvarId
  return attach ps k

/--
Similar to `attachFVarDeps`. Extract from the state any local function declarations that depends on the given
parameters, **and** attach to code `k`.
-/
def attachParamsDeps (params : Array (Param ph)) (k : Code ph) : PullM ph (Code ph) := do
  let ps ← findParamsDeps params
  return attach ps k

def attachJps (k : Code ph) : PullM ph (Code ph) := do
  let jps := (← get).filter fun info => !info.isFun
  modify fun s => s.filter fun info => info.isFun
  let jps ← findFVarDepsFixpoint jps
  return attach jps k

mutual
/--
Add local function declaration (or join point if `isFun = false`) to the state.
-/
partial def addToPull (isFun : Bool) (decl : FunDecl ph) : PullM ph Unit := do
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
partial def pull (code : Code ph) : PullM ph (Code ph) := do
  match code with
  | .let decl k =>
    let k ← pull k
    let k ← attachFVarDeps decl.fvarId k
    return code.updateLet! decl k
  | .fun decl k _ => addToPull true decl; pull k
  | .jp decl k => addToPull false decl; pull k
  | .cases c =>
    let alts ← c.alts.mapMonoM fun alt => do
      match alt with
      | .default k => return alt.updateCode (← pull k)
      | .alt _ ps k _ =>
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
def Decl.pullFunDecls (decl : Decl ph) : CompilerM (Decl ph) := do
  let (value, ps) ← decl.value.mapCodeM pull |>.run []
  let value := value.mapCode (attach ps.toArray)
  return { decl with value }

def pullFunDecls : Pass :=
  .mkPerDeclaration `pullFunDecls .base Decl.pullFunDecls

builtin_initialize
  registerTraceClass `Compiler.pullFunDecls (inherited := true)

namespace Lean.Compiler.LCNF
