/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Log
import Lean.Elab.Util

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
    for ns in (← resolveNamespace ns.getId) do
      addOpenDecl (OpenDecl.simple ns [])
      activateScoped ns

private def elabOpenScoped (n : Syntax) : M (m:=m) Unit :=
  -- `open` `scoped` id+
  for ns in n[1].getArgs do
    for ns in (← resolveNamespace ns.getId) do
    activateScoped ns

private def resolveNameUsingNamespacesCore (nss : List Name) (idStx : Syntax) : M (m:=m) Name := do
  let mut exs := #[]
  let mut result := #[]
  for ns in nss do
    try
      let declName ← resolveId ns idStx
      result := result.push declName
    catch ex =>
      exs := exs.push ex
  if exs.size == nss.length then
    withRef idStx do
      if exs.size == 1 then
        throw exs[0]
      else
        throwErrorWithNestedErrors "failed to open" exs
  if result.size == 1 then
    return result[0]
  else
    withRef idStx do throwError "ambiguous identifier '{idStx.getId}', possible interpretations: {result.map mkConst}"

-- `open` id `(` id+ `)`
private def elabOpenOnly (n : Syntax) : M (m:=m) Unit := do
  let nss ← resolveNamespace n[0].getId
  for idStx in n[2].getArgs do
    let declName ← resolveNameUsingNamespacesCore nss idStx
    addOpenDecl (OpenDecl.explicit idStx.getId declName)

-- `open` id `hiding` id+
private def elabOpenHiding (n : Syntax) : M (m:=m) Unit := do
  let ns ← resolveUniqueNamespace n[0].getId
  let mut ids : List Name := []
  for idStx in n[2].getArgs do
    let _ ← resolveId ns idStx
    let id := idStx.getId
    ids := id::ids
  addOpenDecl (OpenDecl.simple ns ids)

-- `open` id `renaming` sepBy (id `->` id) `,`
private def elabOpenRenaming (n : Syntax) : M (m:=m) Unit := do
  let ns ← resolveUniqueNamespace n[0].getId
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

def resolveNameUsingNamespaces [MonadResolveName m] (nss : List Name) (idStx : Syntax) : m Name := do
  StateRefT'.run' (s := { openDecls := (← getOpenDecls), currNamespace := (← getCurrNamespace) }) do
    resolveNameUsingNamespacesCore nss idStx

end OpenDecl

export OpenDecl (elabOpenDecl resolveOpenDeclId resolveNameUsingNamespaces)

end Lean.Elab
