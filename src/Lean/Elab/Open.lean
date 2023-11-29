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

/--
A local copy of name resolution state that allows us to immediately use new open decls
in further name resolution as in `open Lean Elab`.
-/
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
        throw exs[0]!
      else
        throwErrorWithNestedErrors "failed to open" exs
  if result.size == 1 then
    return result[0]!
  else
    withRef idStx do throwError "ambiguous identifier '{idStx.getId}', possible interpretations: {result.map mkConst}"

def elabOpenDecl [MonadResolveName m] [MonadInfoTree m] (stx : TSyntax ``Parser.Command.openDecl) : m (List OpenDecl) := do
  StateRefT'.run' (s := { openDecls := (← getOpenDecls), currNamespace := (← getCurrNamespace) }) do
    match stx with
    | `(Parser.Command.openDecl| $nss*) =>
      for ns in nss do
        for ns in (← resolveNamespace ns) do
          addOpenDecl (OpenDecl.simple ns [])
          activateScoped ns
    | `(Parser.Command.openDecl| scoped $nss*) =>
      for ns in nss do
        for ns in (← resolveNamespace ns) do
          activateScoped ns
    | `(Parser.Command.openDecl| $ns ($ids*)) =>
      let nss ← resolveNamespace ns
      for idStx in ids do
        let declName ← resolveNameUsingNamespacesCore nss idStx
        if (← getInfoState).enabled then
          addConstInfo idStx declName
        addOpenDecl (OpenDecl.explicit idStx.getId declName)
    | `(Parser.Command.openDecl| $ns hiding $ids*) =>
      let ns ← resolveUniqueNamespace ns
      activateScoped ns
      for id in ids do
        let declName ← resolveId ns id
        if (← getInfoState).enabled then
          addConstInfo id declName
      let ids := ids.map (·.getId) |>.toList
      addOpenDecl (OpenDecl.simple ns ids)
    | `(Parser.Command.openDecl| $ns renaming $[$froms -> $tos],*) =>
      let ns ← resolveUniqueNamespace ns
      for («from», to) in froms.zip tos do
        let declName ← resolveId ns «from»
        if (← getInfoState).enabled then
          addConstInfo «from» declName
          addConstInfo to declName
        addOpenDecl (OpenDecl.explicit to.getId declName)
    | _ => throwUnsupportedSyntax
    return (← get).openDecls

def resolveNameUsingNamespaces [MonadResolveName m] (nss : List Name) (idStx : Ident) : m Name := do
  StateRefT'.run' (s := { openDecls := (← getOpenDecls), currNamespace := (← getCurrNamespace) }) do
    resolveNameUsingNamespacesCore nss idStx

end OpenDecl

export OpenDecl (elabOpenDecl resolveNameUsingNamespaces)

end Lean.Elab
