/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.LCNF.Internalize
import Lean.Compiler.LCNF.ElimDead
import Init.Data.ByteArray.Basic

namespace Lean.Compiler.LCNF
/-!
# Function arity reduction

This module finds "used" parameters in a declaration, and then
create an auxiliary declaration that contains only used parameters.
For example:
```
def f (x y : Nat) : Nat :=
  let _x.1 := Nat.add x x
  let _x.2 := Nat.mul _x.1 _x.1
  _x.2
```
is converted into
```
def f._rarg (x : Nat) : Nat :=
  let _x.1 := Nat.add x x
  let _x.2 := Nat.mul _x.1 _x.1
  _x.2
def f (x y : Nat) : Nat :=
  let _x.1 := f._rarg x
  _x.1
```
Note that any `f` full application is going to be inlined in the next `simp` pass.

This module has basic support for detecting "unused" variables in recursive definitions.
For example, the `y` in the following definition in correctly treated as "unused"
```
def f (x y : Nat) : Nat :=
  cases x
  | zero => x
  | succ _x.1 =>
    let _x.2 := f _x.1 y
    let _x.3 := Nat.mul _x.2 _x.2
    _x.3
```
This module does not have similar support for mutual recursive applications.
We assume this limitation is irrelevant in practice.
-/
namespace FindUsed

def mkParamSet (numParams : Nat) : ByteArray := Id.run do
  let mut s := ByteArray.emptyWithCapacity numParams
  for _ in 0...numParams do
    s := s.push 0
  return s

def paramSetSubsumes (s other : ByteArray) (idx? : Option Nat) : Bool := Id.run do
  if let some idx := idx? then
    if s.get! idx == 0 then return false
  for h : i in 0...other.size do
    if other[i] != 0 && s.get! i == 0 then
      return false
  return true

def paramSetUnion (s other : ByteArray) : ByteArray := Id.run do
  let mut s := s
  for h : i in 0...other.size do
    if other[i] != 0 && s.get! i == 0 then
      s := s.set! i 1
  return s

structure Context where
  decl : Decl .pure
  paramIdx : Std.HashMap FVarId Nat
  emptySet : ByteArray

structure State where
  defUseMap : Std.HashMap FVarId ByteArray := {}
  relevantSet : Std.HashSet FVarId := {}
  changed : Bool := true

abbrev FindUsedM := ReaderT Context <| StateRefT State CompilerM

def recordRelevant (fvarId : FVarId) : FindUsedM Unit := do
  modify fun s => { s with relevantSet := s.relevantSet.insert fvarId }

def propagateUse (source : FVarId) (target : FVarId) : FindUsedM Unit := do
  let ctx ← read
  let sourceSet := (← get).defUseMap.getD source ctx.emptySet
  let sourceIdx? := ctx.paramIdx[source]?
  if paramSetSubsumes ((← get).defUseMap.getD target ctx.emptySet) sourceSet sourceIdx? then
    return ()
  modify fun s =>
    { s with
      changed := true
      defUseMap := s.defUseMap.alter target fun set? =>
        let set := paramSetUnion (set?.getD ctx.emptySet) sourceSet
        match sourceIdx? with
        | some idx => set.set! idx 1
        | none => set }

def visitLetDecl (letDecl : LetDecl .pure) : FindUsedM Unit := do
  match letDecl.value with
  | .erased | .lit .. => return ()
  | .proj _ _ fvarId => propagateUse fvarId letDecl.fvarId
  | .fvar fvarId args =>
    propagateUse fvarId letDecl.fvarId
    args.forM (propagateArg · letDecl.fvarId)
  | .const declName _ args =>
    let decl := (← read).decl
    if declName == decl.name then
      for param in decl.params, arg in args do
        propagateArg arg param.fvarId
      -- over-application
      for arg in args[decl.params.size...*] do
        propagateArg arg letDecl.fvarId
      -- partial-application
      for param in decl.params[args.size...*] do
        -- If recursive function is partially applied, we assume missing parameters are used because we don't want to eta-expand.
        propagateUse param.fvarId letDecl.fvarId
    else
      args.forM (propagateArg · letDecl.fvarId)
where
  propagateArg (source : Arg .pure) (target : FVarId) : FindUsedM Unit := do
    if let .fvar source := source then
      propagateUse source target

partial def visit (code : Code .pure) : FindUsedM Unit := do
  match code with
  | .let decl k =>
    visitLetDecl decl
    visit k
  | .jp decl k | .fun decl k =>
    visit k
    visit decl.value
  | .cases c =>
    recordRelevant c.discr
    c.alts.forM fun alt => visit alt.getCode
  | .jmp fvarId args =>
    let decl ← getFunDecl (pu := .pure) fvarId
    for arg in args, param in decl.params do
      if let .fvar arg := arg then
        propagateUse arg param.fvarId
  | .return fvarId => recordRelevant fvarId
  | .unreach _ => return ()

partial def collectJpParams (code : Code .pure) (s : Std.HashMap FVarId Nat) :
    Std.HashMap FVarId Nat :=
  match code with
  | .let _ k => collectJpParams k s
  | .fun decl k => collectJpParams k (collectJpParams decl.value s)
  | .jp decl k =>
    let s := decl.params.foldl (init := s) fun s param => s.insertIfNew param.fvarId s.size
    collectJpParams k (collectJpParams decl.value s)
  | .cases c => c.alts.foldl (init := s) fun s alt => collectJpParams alt.getCode s
  | .jmp .. | .return .. | .unreach .. => s

partial def collectUsedParams (decl : Decl .pure) : CompilerM FVarIdHashSet := do
  let paramIdx := decl.params.foldl (init := {}) fun s p => s.insertIfNew p.fvarId s.size
  let .code code := decl.value | unreachable!
  let paramIdx := collectJpParams code paramIdx
  let emptySet := mkParamSet paramIdx.size
  let (used, _) ← go |>.run { decl, paramIdx, emptySet } |>.run {}
  return used
where
  go : FindUsedM FVarIdHashSet := do
    decl.value.forCodeM visit
    if (← get).changed then
      modify fun s => { s with changed := false }
      go
    else
      let ctx ← read
      let mut used := ctx.emptySet
      for relevantFVar in (← get).relevantSet do
        if let some idx := ctx.paramIdx[relevantFVar]? then
          used := used.set! idx 1
        used := paramSetUnion used ((← get).defUseMap.getD relevantFVar ctx.emptySet)
      let mut result : FVarIdHashSet := {}
      for (fvarId, idx) in ctx.paramIdx do
        if used.get! idx != 0 then
          result := result.insert fvarId
      return result

end FindUsed

namespace ReduceArity

structure Context where
  declName : Name
  auxDeclName : Name
  paramMask : Array Bool
  allUnused : Bool
  used : FVarIdHashSet
  jpMasks : Std.HashMap FVarId (Array Bool) := {}

abbrev ReduceM := ReaderT Context CompilerM

partial def reduce (code : Code .pure) : ReduceM (Code .pure) := do
  match code with
  | .let decl k =>
    let .const declName _ args := decl.value | do return code.updateLet! decl (← reduce k)
    unless declName == (← read).declName do return code.updateLet! decl (← reduce k)
    let mut argsNew := #[]
    let mask := (← read).paramMask
    if (← read).allUnused then
      argsNew := #[.erased]
      -- keep over-application
      argsNew := argsNew ++ args.drop mask.size
    else
      for h : i in *...args.size do
        -- keep over-application
        if mask.getD i true then
          argsNew := argsNew.push args[i]
    let decl ← decl.updateValue (.const (← read).auxDeclName [] argsNew)
    return code.updateLet! decl (← reduce k)
  | .fun decl k =>
    let decl ← decl.updateValue (← reduce decl.value)
    return code.updateFun! decl (← reduce k)
  | .jp decl k =>
    let used := (← read).used
    let mask := decl.params.map fun param => used.contains param.fvarId
    if mask.all id then
      let decl ← decl.updateValue (← reduce decl.value)
      return code.updateFun! decl (← reduce k)
    withReader (fun ctx => { ctx with jpMasks := ctx.jpMasks.insert decl.fvarId mask }) do
      let value ← reduce decl.value
      let k ← reduce k
      let mut paramsNew := #[]
      for keep in mask, param in decl.params do
        if keep then
          paramsNew := paramsNew.push param
        else
          eraseParam param
      let type ← mkForallParams paramsNew (← value.inferType)
      let decl ← decl.update type paramsNew value
      return .jp decl k
  | .cases c =>
    let alts ← c.alts.mapMonoM fun alt => return alt.updateCode (← reduce alt.getCode)
    return code.updateAlts! alts
  | .jmp fvarId args =>
    let some mask := (← read).jpMasks.get? fvarId | return code
    let mut argsNew := #[]
    for keep in mask, arg in args do
      if keep then
        argsNew := argsNew.push arg
    return .jmp fvarId argsNew
  | .unreach .. | .return .. => return code

end ReduceArity

open FindUsed ReduceArity Internalize

public def Decl.reduceArity (decl : Decl .pure) : CompilerM (Array (Decl .pure)) := do
  match decl.value with
  | .code code =>
    if decl.params.isEmpty then
      return #[decl]
    let used ← collectUsedParams decl
    let mask := decl.params.map fun param => used.contains param.fvarId
    if mask.all id then
      -- Do nothing if all params were used
      return #[decl]

    -- If all parameters are unused we introduce a dummy void parameter to avoid promoting the
    -- declaration to a constant
    let allUnused := !mask.any id
    let usedParams := decl.params.filter fun param => used.contains param.fvarId
    trace[Compiler.reduceArity] "{decl.name}, used params: {usedParams.toList.map (mkFVar ·.fvarId)}"
    let auxName   := decl.name ++ `_redArg
    let mkAuxDecl : CompilerM (Decl .pure) := do
      let params ←
        if allUnused then
          pure #[← mkParam `_dummy ImpureType.void false]
        else
          pure usedParams
      let ctx := { declName := decl.name, auxDeclName := auxName, paramMask := mask, allUnused, used }
      let code ← reduce code |>.run ctx
      let type ← mkForallParams params (← code.inferType)
      let auxDecl := { decl with name := auxName, levelParams := [], type, params, value := .code code }
      let auxDecl ← auxDecl.elimDeadVars
      auxDecl.saveMono
      return auxDecl
    let updateDecl : InternalizeM .pure (Decl .pure) := do
      let params ← decl.params.mapM internalizeParam
      let mut args := #[]
      if allUnused then
        args := #[.erased]
      else
        for used in mask, param in params do
          if used then
            args := args.push param.toArg
      let letDecl ← mkAuxLetDecl (.const auxName [] args)
      let value := .code (.let letDecl (.return letDecl.fvarId))
      let decl := { decl with params, value, inlineAttr? := some .inline, recursive := false }
      decl.saveMono
      return decl
    let unusedParams := decl.params.filter fun param => !used.contains param.fvarId
    let auxDecl ← mkAuxDecl
    let decl ← updateDecl |>.run' {}
    eraseParams unusedParams
    return #[auxDecl, decl]
  | .extern .. => return #[decl]

public def reduceArity : Pass where
  phase := .mono
  phaseOut := .mono
  name  := `reduceArity
  run   := fun decls => do
    decls.foldlM (init := #[]) fun decls decl => return decls ++ (← decl.reduceArity)

builtin_initialize
  registerTraceClass `Compiler.reduceArity (inherited := true)

end Lean.Compiler.LCNF
