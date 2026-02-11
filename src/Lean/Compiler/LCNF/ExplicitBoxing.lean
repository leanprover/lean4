/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM
public import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.ElimDead
import Lean.Runtime

namespace Lean.Compiler.LCNF

open ImpureType

structure Ctx where
  currDecl : Name
  currDeclResultType : Expr
-- TODO: use auxdeclcache for caching auxiliary decls
  decls : Array (Decl .impure)

structure State where
  auxDecls : Array (Decl .impure) := #[]
  nextAuxIdx : Nat := 1

abbrev BoxM := ReaderT Ctx StateRefT State CompilerM

def requiresBoxedVersion (sig : Signature .impure) : CompilerM Bool := do
  let ps := sig.params
  let env ← getEnv
  return (ps.size > 0
    && (sig.type.isScalar
      || ps.any (fun p => p.type.isScalar || p.borrow || p.type.isVoid)
      || isExtern env sig.name))
    || ps.size > closureMaxArgs

def mkBoxedVersion (decl : Decl .impure) : CompilerM (Decl .impure) := do
  sorry

public def addBoxedVersions (decls : Array (Decl .impure)) : CompilerM (Array (Decl .impure)) := do
  let boxedDecls ← decls.filterMapM fun decl => do
    if ← requiresBoxedVersion decl.toSignature then
      let boxed ← mkBoxedVersion decl
      return some boxed
    else
      return none
  return decls ++ boxedDecls

def run (decls : Array (Decl .impure)) : CompilerM (Array (Decl .impure)) := do
  let decls ← decls.foldlM (init := #[]) fun newDecls decl => do
    match decl.value with
    | .code code => sorry
    | .extern .. => return newDecls.push decl
  addBoxedVersions decls


public def explicitBoxing : Pass where
  phase := .impure
  phaseOut := .impure
  name := `boxing
  run := run

builtin_initialize
  registerTraceClass `Compiler.explicitBoxing (inherited := true)

end Lean.Compiler.LCNF
