/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.MonadEnv
public import Lean.Util.FoldConsts

public section

namespace Lean

private structure State where
  visited : NameSet    := {}
  axioms  : Array Name := #[]

partial def collectAxioms [Monad m] [MonadEnv m] [MonadError m] (constName : Name) : m (Array Name) := do
  let (_, s) ← (collect constName).run {}
  pure s.axioms
where collect (c : Name) : StateT State m Unit := do
  let collectExpr (e : Expr) : StateT State m Unit := e.getUsedConstants.forM collect
  let s ← get
  unless s.visited.contains c do
    modify fun s => { s with visited := s.visited.insert c }
    let env ← getEnv
    -- We should take the constant from the kernel env, which may differ from the one in the elab
    -- env in case of (async) errors.
    match env.checked.get.find? c with
    | some (ConstantInfo.axiomInfo v)  =>
        modify fun s => { s with axioms := (s.axioms.push c) }
        collectExpr v.type
    | some (ConstantInfo.defnInfo v)   => collectExpr v.type *> collectExpr v.value
    | some (ConstantInfo.thmInfo v)    => collectExpr v.type *> collectExpr v.value
    | some (ConstantInfo.opaqueInfo v) => collectExpr v.type *> collectExpr v.value
    | some (ConstantInfo.quotInfo _)   => pure ()
    | some (ConstantInfo.ctorInfo v)   => collectExpr v.type
    | some (ConstantInfo.recInfo v)    => collectExpr v.type
    | some (ConstantInfo.inductInfo v) => collectExpr v.type *> v.ctors.forM collect
    | none                             => liftM (m := m) <| throwError "unknown constant '{c}'"

end Lean
