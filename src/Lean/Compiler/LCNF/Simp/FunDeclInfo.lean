/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Compiler.LCNF.Simp.Basic

namespace Lean.Compiler.LCNF
namespace Simp

/--
Local function usage information used to decide whether it should be inlined or not.
The information is an approximation, but it is on the "safe" side. That is, if we tagged
a function with `.once`, then it is applied only once. A local function may be marked as
`.many`, but after simplifications the number of applications may reduce to 1. This is not
a big problem in practice because we run the simplifier multiple times, and this information
is recomputed from scratch at the beginning of each simplification step.
-/
inductive FunDeclInfo where
  /--
  Local function is applied once, and must be inlined.
  -/
  | once
  /--
  Local function is applied many times or occur as an argument of another function,
  and will only be inlined if it is small.
  -/
  | many
  /--
  Function must be inlined.
  -/
  | mustInline
  deriving Repr, Inhabited

/--
Local function declaration statistics.
-/
structure FunDeclInfoMap where
  /--
  Mapping from local function name to inlining information.
  -/
  map : Std.HashMap FVarId FunDeclInfo := {}
  deriving Inhabited

def FunDeclInfoMap.format (s : FunDeclInfoMap) : CompilerM Format := do
  let mut result := Format.nil
  for (fvarId, info) in s.map.toList do
    let binderName ← getBinderName fvarId
    result := result ++ "\n" ++ f!"{binderName} ↦ {repr info}"
  return result

/--
Add new occurrence for the local function with binder name `key`.
-/
def FunDeclInfoMap.add (s : FunDeclInfoMap) (fvarId : FVarId) : FunDeclInfoMap :=
  match s with
  | { map } =>
    match map[fvarId]? with
    | some .once => { map := map.insert fvarId .many }
    | none       => { map := map.insert fvarId .once }
    | _          => { map }

/--
Add new occurrence for the local function occurring as an argument for another function.
-/
def FunDeclInfoMap.addHo (s : FunDeclInfoMap) (fvarId : FVarId) : FunDeclInfoMap :=
  match s with
  | { map } =>
    match map[fvarId]? with
    | some .once | none => { map := map.insert fvarId .many }
    | _ => { map }

/--
Add new occurrence for the local function with binder name `key`.
-/
def FunDeclInfoMap.addMustInline (s : FunDeclInfoMap) (fvarId : FVarId) : FunDeclInfoMap :=
  match s with
  | { map } => { map := map.insert fvarId .mustInline }

def FunDeclInfoMap.restore (s : FunDeclInfoMap) (fvarId : FVarId) (saved? : Option FunDeclInfo) : FunDeclInfoMap :=
  match s, saved? with
  | { map }, none => { map := map.erase fvarId }
  | { map }, some saved => { map := map.insert fvarId saved }

/--
Traverse `code` and update function occurrence map.
This map is used to decide whether we inline local functions or not.
If `mustInline := true`, then all local function declarations occurring in
`code` are tagged as `.mustInline`.
Recall that we use `.mustInline` for local function declarations occurring in type class instances.
-/
partial def FunDeclInfoMap.update (s : FunDeclInfoMap) (code : Code) (mustInline := false) : CompilerM FunDeclInfoMap := do
  let (_, s) ← go code |>.run s
  return s
where
  addArgOcc (arg : Arg) : StateRefT FunDeclInfoMap CompilerM Unit := do
    match arg with
    | .fvar fvarId =>
      let some funDecl ← findFunDecl'? fvarId | return ()
      modify fun s => s.addHo funDecl.fvarId
    | .erased .. | .type .. => return ()

  addLetValueOccs (e : LetValue) : StateRefT FunDeclInfoMap CompilerM Unit := do
    match e with
    | .erased | .value .. | .proj .. => return ()
    | .const _ _ args => args.forM addArgOcc
    | .fvar fvarId args =>
      let some funDecl ← findFunDecl'? fvarId | return ()
      modify fun s => s.add funDecl.fvarId
      args.forM addArgOcc

  go (code : Code) : StateRefT FunDeclInfoMap CompilerM Unit := do
    match code with
    | .let decl k =>
      addLetValueOccs decl.value
      go k
    | .fun decl k =>
      if mustInline then
        modify fun s => s.addMustInline decl.fvarId
      go decl.value; go k
    | .jp decl k => go decl.value; go k
    | .cases c => c.alts.forM fun alt => go alt.getCode
    | .jmp fvarId args =>
      let funDecl ← getFunDecl fvarId
      modify fun s => s.add funDecl.fvarId
      args.forM addArgOcc
    | .return .. | .unreach .. => return ()

end Simp
end Lean.Compiler.LCNF
