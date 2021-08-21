/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Log

namespace Lean.Elab
namespace OpenDecl

variable [Monad m] [STWorld IO.RealWorld m] [MonadEnv m]
variable [MonadExceptOf Exception m] [MonadRef m] [AddErrorMessageContext m]
variable [AddMessageContext m] [MonadLiftT (ST IO.RealWorld) m] [MonadLog m]

structure State where
  openDecls     : List OpenDecl
  currNamespace : Name

abbrev M := StateRefT State m

instance : MonadResolveName (M (m := m)) where
  getCurrNamespace   := return (← get).currNamespace
  getOpenDecls       := return (← get).openDecls

def resolveId (ns : Name) (idStx : Syntax) : M (m := m) Name := do
  let declName := ns ++ idStx.getId
  if (← getEnv).contains declName then
    return declName
  else
    withRef idStx <| resolveGlobalConstNoOverloadCore declName

private def addOpenDecl (decl : OpenDecl) : M (m:=m) Unit :=
  modify fun s => { s with openDecls := decl :: s.openDecls }

private def elabOpenSimple (n : Syntax) : M (m:=m) Unit :=
  -- `open` id+
  for ns in n[0].getArgs do
    let ns ← resolveNamespace ns.getId
    addOpenDecl (OpenDecl.simple ns [])
    activateScoped ns

private def elabOpenScoped (n : Syntax) : M (m:=m) Unit :=
  -- `open` `scoped` id+
  for ns in n[1].getArgs do
    activateScoped (← resolveNamespace ns.getId)

-- `open` id `(` id+ `)`
private def elabOpenOnly (n : Syntax) : M (m:=m) Unit := do
  let ns ← resolveNamespace n[0].getId
  for idStx in n[2].getArgs do
    let declName ← resolveId ns idStx
    addOpenDecl (OpenDecl.explicit idStx.getId declName)

-- `open` id `hiding` id+
private def elabOpenHiding (n : Syntax) : M (m:=m) Unit := do
  let ns ← resolveNamespace n[0].getId
  let mut ids : List Name := []
  for idStx in n[2].getArgs do
    let declName ← resolveId ns idStx
    let id := idStx.getId
    ids := id::ids
  addOpenDecl (OpenDecl.simple ns ids)

-- `open` id `renaming` sepBy (id `->` id) `,`
private def elabOpenRenaming (n : Syntax) : M (m:=m) Unit := do
  let ns ← resolveNamespace n[0].getId
  for stx in n[2].getSepArgs do
    let fromStx  := stx[0]
    let toId     := stx[2].getId
    let declName ← resolveId ns fromStx
    addOpenDecl (OpenDecl.explicit toId declName)

def elabOpenDecl [MonadResolveName m] (openDeclStx : Syntax) : m (List OpenDecl) := do
  StateRefT'.run' (s := { openDecls := (← getOpenDecls), currNamespace := (← getCurrNamespace) }) do
    if openDeclStx.getKind == ``Parser.Command.openSimple then
      elabOpenSimple openDeclStx
    else if openDeclStx.getKind == ``Parser.Command.openScoped then
      elabOpenScoped openDeclStx
    else if openDeclStx.getKind == ``Parser.Command.openOnly then
      elabOpenOnly openDeclStx
    else if openDeclStx.getKind == ``Parser.Command.openHiding then
      elabOpenHiding openDeclStx
    else
      elabOpenRenaming openDeclStx
    return (← get).openDecls

def resolveOpenDeclId [MonadResolveName m] (ns : Name) (idStx : Syntax) : m Name := do
  StateRefT'.run' (s := { openDecls := (← getOpenDecls), currNamespace := (← getCurrNamespace) }) do
    OpenDecl.resolveId ns idStx

end OpenDecl

export OpenDecl (elabOpenDecl resolveOpenDeclId)

end Lean.Elab
