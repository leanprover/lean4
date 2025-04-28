/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.CoreM

namespace Lean

private builtin_initialize exportedAxiomsExt : MapDeclarationExtension (Array Name) ← mkMapDeclarationExtension

namespace CollectAxioms

structure State where
  visited : NameSet    := {}
  axioms  : Array Name := #[]

abbrev M := ReaderT Environment $ StateM State

private partial def collect (c : Name) : M Unit := do
  let collectExpr (e : Expr) : M Unit := e.getUsedConstants.forM collect
  let s ← get
  unless s.visited.contains c do
    modify fun s => { s with visited := s.visited.insert c }
    let env ← read
    if let some axioms := exportedAxiomsExt.find? env c then
      for ax in axioms do
        if ax == c then
          modify fun s => { s with axioms := s.axioms.push c }
        else
          collect ax
      return
    -- We should take the constant from the kernel env, which may differ from the one in the elab
    -- env in case of (async) errors.
    match env.checked.get.find? c with
    | some (ConstantInfo.axiomInfo _)  => modify fun s => { s with axioms := s.axioms.push c }
    | some (ConstantInfo.defnInfo v)   => collectExpr v.type *> collectExpr v.value
    | some (ConstantInfo.thmInfo v)    => collectExpr v.type *> collectExpr v.value
    | some (ConstantInfo.opaqueInfo v) => collectExpr v.type *> collectExpr v.value
    | some (ConstantInfo.quotInfo _)   => pure ()
    | some (ConstantInfo.ctorInfo v)   => collectExpr v.type
    | some (ConstantInfo.recInfo v)    => collectExpr v.type
    | some (ConstantInfo.inductInfo v) => collectExpr v.type *> v.ctors.forM collect
    | none                             => pure ()

end CollectAxioms

def collectAxioms [Monad m] [MonadEnv m] (constName : Name) : m (Array Name) := do
  let env ← getEnv
  let (_, s) := ((CollectAxioms.collect constName).run env).run {}
  pure s.axioms

/--
Registers axioms used by the declaration in an environment extension so they can be retrieved even
if some parts of the declaration's become inaccessible.
-/
def registerAxiomsForDecl (n : Name) : CoreM Unit := do
  let axioms ← collectAxioms n
  modifyEnv (exportedAxiomsExt.addEntry · (n, axioms))

end Lean
