/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.InferType
import Lean.Compiler.LCNF.Internalize

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

structure Context where
  decl : Decl
  params : FVarIdSet

structure State where
  used : FVarIdSet := {}

abbrev FindUsedM := ReaderT Context <| StateRefT State CompilerM

def visitFVar (fvarId : FVarId) : FindUsedM Unit := do
  if (← read).params.contains fvarId then
    modify fun s => { s with used := s.used.insert fvarId }

def visitArg (arg : Arg) : FindUsedM Unit := do
  match arg with
  | .erased | .type .. => return ()
  | .fvar fvarId => visitFVar fvarId

def visitLetValue (e : LetValue) : FindUsedM Unit := do
  match e with
  | .erased | .value .. => return ()
  | .proj _ _ fvarId => visitFVar fvarId
  | .fvar fvarId args => visitFVar fvarId; args.forM visitArg
  | .const declName _ args =>
    let decl := (← read).decl
    if declName == decl.name then
      for param in decl.params, arg in args do
        match arg with
        | .fvar fvarId =>
          unless fvarId == param.fvarId do
            visitFVar fvarId
        | .erased | .type .. => pure ()
      -- over-application
      for arg in args[decl.params.size:] do
        visitArg arg
      -- partial-application
      for param in decl.params[args.size:] do
        -- If recursive function is partially applied, we assume missing parameters are used because we don't want to eta-expand.
        visitFVar param.fvarId
    else
      args.forM visitArg

partial def visit (code : Code) : FindUsedM Unit := do
  match code with
  | .let decl k =>
    visitLetValue decl.value
    visit k
  | .jp decl k | .fun decl k =>
    visit decl.value; visit k
  | .cases c =>
    visitFVar c.discr
    c.alts.forM fun alt => visit alt.getCode
  | .jmp _ args => args.forM visitArg
  | .return fvarId => visitFVar fvarId
  | .unreach _ => return ()

def collectUsedParams (decl : Decl) : CompilerM FVarIdSet := do
  let params := decl.params.foldl (init := {}) fun s p => s.insert p.fvarId
  let (_, { used, .. }) ← visit decl.value |>.run { decl, params } |>.run {}
  return used

end FindUsed

namespace ReduceArity

structure Context where
  declName : Name
  auxDeclName : Name
  paramMask : Array Bool

abbrev ReduceM := ReaderT Context CompilerM

partial def reduce (code : Code) : ReduceM Code := do
  match code with
  | .let decl k =>
    let .const declName _ args := decl.value | do return code.updateLet! decl (← reduce k)
    unless declName == (← read).declName do return code.updateLet! decl (← reduce k)
    let mut argsNew := #[]
    for used in (← read).paramMask, arg in args do
      if used then
        argsNew := argsNew.push arg
    let decl ← decl.updateValue (.const (← read).auxDeclName [] argsNew)
    return code.updateLet! decl (← reduce k)
  | .fun decl k | .jp decl k =>
    let decl ← decl.updateValue (← reduce decl.value)
    return code.updateFun! decl (← reduce k)
  | .cases c =>
    let alts ← c.alts.mapMonoM fun alt => return alt.updateCode (← reduce alt.getCode)
    return code.updateAlts! alts
  | .unreach .. | .jmp .. | .return .. => return code

end ReduceArity

open FindUsed ReduceArity Internalize

def Decl.reduceArity (decl : Decl) : CompilerM (Array Decl) := do
  let used ← collectUsedParams decl
  if used.size == decl.params.size then
    return #[decl] -- Declarations uses all parameters
  else
    trace[Compiler.reduceArity] "{decl.name}, used params: {used.toList.map mkFVar}"
    let mask   := decl.params.map fun param => used.contains param.fvarId
    let auxName   := decl.name ++ `_redArg
    let mkAuxDecl : CompilerM Decl := do
      let params := decl.params.filter fun param => used.contains param.fvarId
      let value  ← reduce decl.value |>.run { declName := decl.name, auxDeclName := auxName, paramMask := mask }
      let type ← value.inferType
      let type ← mkForallParams params type
      let auxDecl := { decl with name := auxName, levelParams := [], type, params, value }
      auxDecl.saveMono
      return auxDecl
    let updateDecl : InternalizeM Decl := do
      let params ← decl.params.mapM internalizeParam
      let mut args := #[]
      for used in mask, param in params do
        if used then
          args := args.push param.toArg
      let letDecl ← mkAuxLetDecl (.const auxName [] args)
      let value := .let letDecl (.return letDecl.fvarId)
      let decl := { decl with params, value, inlineAttr? := some .inline, recursive := false }
      decl.saveMono
      return decl
    let unusedParams := decl.params.filter fun param => !used.contains param.fvarId
    let auxDecl ← mkAuxDecl
    let decl ← updateDecl |>.run' {}
    eraseParams unusedParams
    return #[auxDecl, decl]

def reduceArity : Pass where
  phase := .mono
  name  := `reduceArity
  run   := fun decls => do
    decls.foldlM (init := #[]) fun decls decl => return decls ++ (← decl.reduceArity)

builtin_initialize
  registerTraceClass `Compiler.reduceArity (inherited := true)

end Lean.Compiler.LCNF