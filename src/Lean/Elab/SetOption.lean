/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Log
import Lean.Elab.InfoTree
namespace Lean.Elab

variable [Monad m] [MonadOptions m] [MonadExceptOf Exception m] [MonadRef m]
variable [AddErrorMessageContext m] [MonadLiftT (EIO Exception) m] [MonadInfoTree m]

def elabSetOption (id : Syntax) (val : Syntax) : m Options := do
  let ref ← getRef
  -- For completion purposes, we discard `val` and any later arguments.
  -- We include the first argument (the keyword) for position information in case `id` is `missing`.
  addCompletionInfo <| CompletionInfo.option (ref.setArgs (ref.getArgs[0:2]))
  let optionName := id.getId.eraseMacroScopes
  match val.isStrLit? with
  | some str => setOption optionName (DataValue.ofString str)
  | none     =>
  match val.isNatLit? with
  | some num => setOption optionName (DataValue.ofNat num)
  | none     =>
  match val with
  | Syntax.atom _ "true"  => setOption optionName (DataValue.ofBool true)
  | Syntax.atom _ "false" => setOption optionName (DataValue.ofBool false)
  | _ =>
    throwError "unexpected set_option value {val}"
where
  setOption (optionName : Name) (val : DataValue) : m Options := do
    let ref ← getRef
    let decl ← IO.toEIO (fun (ex : IO.Error) => Exception.error ref ex.toString) (getOptionDecl optionName)
    unless decl.defValue.sameCtor val do throwError "type mismatch at set_option"
    return (← getOptions).insert optionName val

end Lean.Elab
