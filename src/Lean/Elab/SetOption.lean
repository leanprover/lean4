/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Log
import Lean.Elab.InfoTree
namespace Lean.Elab

variable [Monad m] [MonadOptions m] [MonadError m] [MonadLiftT (EIO Exception) m] [MonadInfoTree m]

def elabSetOption (id : Syntax) (val : Syntax) : m Options := do
  let ref ← getRef
  -- For completion purposes, we discard `val` and any later arguments.
  -- We include the first argument (the keyword) for position information in case `id` is `missing`.
  addCompletionInfo <| CompletionInfo.option (ref.setArgs (ref.getArgs[0:3]))
  let optionName := id.getId.eraseMacroScopes
  let decl ← IO.toEIO (fun (ex : IO.Error) => Exception.error ref ex.toString) (getOptionDecl optionName)
  pushInfoLeaf <| .ofOptionInfo { stx := id, optionName, declName := decl.declName }
  let rec setOption (val : DataValue) : m Options := do
    unless decl.defValue.sameCtor val do throwError "type mismatch at set_option"
    return (← getOptions).insert optionName val
  match val.isStrLit? with
  | some str => setOption (DataValue.ofString str)
  | none     =>
  match val.isNatLit? with
  | some num => setOption (DataValue.ofNat num)
  | none     =>
  match val with
  | Syntax.atom _ "true"  => setOption (DataValue.ofBool true)
  | Syntax.atom _ "false" => setOption (DataValue.ofBool false)
  | _ =>
    throwError "unexpected set_option value {val}"

end Lean.Elab
