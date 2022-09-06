/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
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
Sort local function declarations and join points being pulled.
We use an order with the following properties.
- If `p₁` depends on `p₂`, then `p₁` is smaller than `p₂`.
- Local function declarations are smaller than join points.
- We break ties using the free variable id.

If the output is of the form `#[p₁, p₂, ...]`, and we have code `c`,
we construct code of the form `... fun p₂.decl <| fun p₁.decl c`
-/
def sortDeps (ps : List ToPull) : Array ToPull :=
  let ps := ps.toArray
  ps.qsort fun p₁ p₂ =>
    if p₂.used.contains p₁.decl.fvarId then
      /- p₂ depends on p₁ -/
      false
    else if p₁.used.contains p₂.decl.fvarId then
      /- p₁ depends on p₂ -/
      true
    else if !p₁.isFun && p₂.isFun then
      /- We want join points to occur before local function declarations whenever possible. -/
      false
    else if p₁.isFun && !p₂.isFun then
      true
    else
      /- Use free variable id as tie breaker. -/
      Name.quickLt p₁.decl.fvarId.name p₂.decl.fvarId.name

/--
Extract from the state any local function declarations that depends on the given
free variable. The idea is that we have to stop pulling these declarations because they
depend on `fvarId`.
-/
def findFVarDeps (fvarId : FVarId) : PullM (List ToPull) := do
  let s ← get
  unless s.any fun info => info.used.contains fvarId do
    return []
  let (s₁, s₂) := go s [] []
  set s₁
  return s₂
where
  go (as keep dep : List ToPull) : List ToPull × List ToPull :=
    match as with
    | [] => (keep ,dep)
    | a :: as =>
      if a.used.contains fvarId then
        go as keep (a :: dep)
      else
        go as (a :: keep) dep

/--
Construct the code `fun p.decl k` or `jp p.decl k`.
-/
def ToPull.attach (p : ToPull) (k : Code) : Code :=
  if p.isFun then
    .fun p.decl k
  else
    .jp p.decl k

mutual
/--
Extract from the state any local function declarations that depends on the given
free variable, **and** attach to code `k`.
-/
partial def attachFVarDeps (fvarId : FVarId) (k : Code) : PullM Code := do
  let ps ← findFVarDeps fvarId
  attach ps k

/--
Attach the given list of local function declarations and join points to `k`.
We also attach any declaration on the state that depends on a `p` in `ps`.
-/
partial def attach (ps : List ToPull) (k : Code) : PullM Code := do
  let mut k := k
  for p in sortDeps ps do
    k ← attachFVarDeps p.decl.fvarId k
    k := p.attach k
  return k
end


/--
Similar to `findFVarDeps`. Extract from the state any local function declarations that depends on the given
parameters.
-/
def findParamsDeps (params : Array Param) : PullM (List ToPull) := do
  let s ← get
  unless s.any fun info => params.any fun p => info.used.contains p.fvarId do
    return []
  let (s₁, s₂) := go s [] []
  set s₁
  return s₂
where
  go (as keep dep : List ToPull) : List ToPull × List ToPull :=
    match as with
    | [] => (keep ,dep)
    | a :: as =>
      if params.any fun p => a.used.contains p.fvarId then
        go as keep (a :: dep)
      else
        go as (a :: keep) dep

/--
Similar to `attachFVarDeps`. Extract from the state any local function declarations that depends on the given
parameters, **and** attach to code `k`.
-/
def attachParamsDeps (params : Array Param) (k : Code) : PullM Code := do
  let ps ← findParamsDeps params
  attach ps k

mutual
/--
Add local function declaration (or join point if `isFun = false`) to the state.
-/
partial def addToPull (isFun : Bool) (decl : FunDecl) : PullM Unit := do
  let value ← pull decl.value
  let value ← attachParamsDeps decl.params value
  let decl ← decl.update' decl.type value
  modify fun s => { isFun, decl, used := decl.collectUsed } :: s

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
  let value ← attach ps value |>.run' []
  return { decl with value }

def pullFunDecls : Pass :=
  .mkPerDeclaration `pullFunDecls Decl.pullFunDecls

builtin_initialize
  registerTraceClass `Compiler.pullFunDecls (inherited := true)

namespace Lean.Compiler.LCNF
