/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.LCNF.Simp.SimpM
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Omega

public section

namespace Lean.Compiler.LCNF
namespace Simp

/--
Mark `fvarId` as an used free variable.
This is information is used to eliminate dead local declarations.
-/
def markUsedFVar (fvarId : FVarId) : SimpM Unit :=
  modify fun s => { s with used := s.used.insert fvarId }

/--
Mark all free variables occurring in `arg` as used.
-/
def markUsedArg (arg : Arg .pure) : SimpM Unit :=
  match arg with
  | .fvar fvarId => markUsedFVar fvarId
  -- Locally declared variables do not occur in types.
  | .type _ | .erased => return ()

/--
Mark all free variables occurring in `e` as used.
-/
def markUsedLetValue (e : LetValue .pure) : SimpM Unit := do
  match e with
  | .lit .. | .erased => return ()
  | .proj _ _ fvarId => markUsedFVar fvarId
  | .const _ _ args => args.forM markUsedArg
  | .fvar fvarId args => markUsedFVar fvarId; args.forM markUsedArg

/--
Mark all free variables occurring on the right-hand side of the given let declaration as used.
This is information is used to eliminate dead local declarations.
-/
def markUsedLetDecl (letDecl : LetDecl .pure) : SimpM Unit :=
  markUsedLetValue letDecl.value

mutual
/--
Mark all free variables occurring in `code` as used.
-/
partial def markUsedCode (code : Code .pure) : SimpM Unit := do
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
partial def markUsedFunDecl (funDecl : FunDecl .pure) : SimpM Unit :=
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
def attachCodeDecls (decls : Array (CodeDecl .pure)) (code : Code .pure) : SimpM (Code .pure) := do
  go decls.size code
where
  go (i : Nat) (code : Code .pure) : SimpM (Code .pure) := do
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
