/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.Simp.SimpM

namespace Lean.Compiler.LCNF
namespace Simp

/--
Mark `fvarId` as an used free variable.
This is information is used to eliminate dead local declarations.
-/
def markUsedFVar (fvarId : FVarId) : SimpM Unit :=
  modify fun s => { s with used := s.used.insert fvarId }

/--
Mark all free variables occurring in `type` as used.
This is information is used to eliminate dead local declarations.
-/
def markUsedType (type : Expr) : SimpM Unit :=
  modify fun s => { s with used := collectLocalDeclsType s.used type }

/--
Mark all free variables occurring in `arg` as used.
-/
def markUsedArg (arg : Arg) : SimpM Unit :=
  match arg with
  | .fvar fvarId => markUsedFVar fvarId
  | .type type => markUsedType type
  | .erased => return ()

/--
Mark all free variables occurring in `e` as used.
-/
def markUsedLetValue (e : LetValue) : SimpM Unit := do
  match e with
  | .value .. | .erased => return ()
  | .proj _ _ fvarId => markUsedFVar fvarId
  | .const _ _ args => args.forM markUsedArg
  | .fvar fvarId args => markUsedFVar fvarId; args.forM markUsedArg

/--
Mark all free variables occurring on the right-hand side of the given let declaration as used.
This is information is used to eliminate dead local declarations.
-/
def markUsedLetDecl (letDecl : LetDecl) : SimpM Unit :=
  markUsedLetValue letDecl.value

mutual
/--
Mark all free variables occurring in `code` as used.
-/
partial def markUsedCode (code : Code) : SimpM Unit := do
  match code with
  | .let decl k => markUsedLetDecl decl; markUsedCode k
  | .jp decl k | .fun decl k => markUsedFunDecl decl; markUsedCode k
  | .return fvarId => markUsedFVar fvarId
  | .unreach .. => return ()
  | .jmp fvarId args => markUsedFVar fvarId; args.forM markUsedArg
  | .cases c => markUsedFVar c.discr; c.alts.forM fun alt => markUsedCode alt.getCode

/--
Mark all free variables occurring in `funDecl` as used.
-/
partial def markUsedFunDecl (funDecl : FunDecl) : SimpM Unit :=
  markUsedCode funDecl.value
end

/--
Return `true` if `fvarId` is in the `used` set.
-/
def isUsed (fvarId : FVarId) : SimpM Bool :=
  return (← get).used.contains fvarId

/--
Attach the given `decls` to `code`. For example, assume `decls` is `#[.let _x.1 := 10, .let _x.2 := true]`,
then the result is
```
let _x.1 := 10
let _x.2 := true
<code>
```
-/
def attachCodeDecls (decls : Array CodeDecl) (code : Code) : SimpM Code := do
  go decls.size code
where
  go (i : Nat) (code : Code) : SimpM Code := do
    if i > 0 then
      let decl := decls[i-1]!
      if (← isUsed decl.fvarId) then
        match decl with
        | .let decl => markUsedLetDecl decl; go (i-1) (.let decl code)
        | .fun decl => markUsedFunDecl decl; go (i-1) (.fun decl code)
        | .jp decl => markUsedFunDecl decl; go (i-1) (.jp decl code)
      else
        eraseCodeDecl decl
        go (i-1) code
    else
      return code
