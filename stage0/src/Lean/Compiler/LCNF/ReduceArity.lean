/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.PhaseExt

namespace Lean.Compiler.LCNF
namespace ReduceArity

/-!
# Function arity reduction

This module finds "used" parameters in a declaration, and then
create an auxliary declaration that contains only used parameters.
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

structure Context where
  decl : Decl
  params : FVarIdSet

structure State where
  used : FVarIdSet := {}

abbrev FindUsedM := ReaderT Context <| StateRefT State CompilerM

def visitFVar (fvarId : FVarId) : FindUsedM Unit := do
  if (← read).params.contains fvarId then
    modify fun s => { s with used := s.used.insert fvarId }

def visitArg (e : Expr) : FindUsedM Unit := do
  let .fvar fvarId := e | return ()
  visitFVar fvarId

def visitExpr (e : Expr) : FindUsedM Unit := do
  match e with
  | .fvar fvarId => visitFVar fvarId
  | .lit .. | .const .. | .sort .. | .forallE .. | .lam .. | .letE .. | .bvar .. | .mvar .. => return ()
  | .mdata _ b => visitExpr b
  | .proj _ _ b => visitExpr b
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    let decl := (← read).decl
    if f.isConstOf decl.name then
      for param in decl.params, arg in args do
        unless arg.isFVarOf param.fvarId do
          visitArg arg
      for arg in args[decl.params.size:] do
        visitArg arg
    else
      visitArg f
      args.forM visitArg

partial def visit (code : Code) : FindUsedM Unit := do
  match code with
  | .let decl k =>
    visitExpr decl.value
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

end ReduceArity
open ReduceArity

def Decl.reduceArity (decl : Decl) : CompilerM Decl := do
  let used ← collectUsedParams decl
  if used.size == decl.params.size then
    return decl -- Declarations uses all parameters
  else
    trace[Compiler.reduceArity] "{decl.name}, used params: {used.toList.map mkFVar}"
    -- TODO: create auxiliary function wth used parameters only
    return decl

def reduceArity : Pass :=
  .mkPerDeclaration `reduceArity (Decl.reduceArity ·) .mono

builtin_initialize
  registerTraceClass `Compiler.reduceArity (inherited := true)

end Lean.Compiler.LCNF