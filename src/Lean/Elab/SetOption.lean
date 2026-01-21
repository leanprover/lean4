/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Elab.InfoTree

public section
namespace Lean.Elab

variable [Monad m] [MonadOptions m] [MonadError m] [MonadLiftT (EIO Exception) m] [MonadInfoTree m]

private def throwUnconfigurable {α} (optionName : Name) : m α :=
  throwError "Invalid `set_option` command: The option `{optionName}` cannot be configured using \
    `set_option`"

/--
Returns the type corresponding to the given `DataValue`, or `none` if the corresponding type
cannot be specified using `set_option` notation.
-/
private def ctorType? : DataValue → Option Expr
  | .ofString .. => mkConst ``String
  | .ofNat .. => mkConst ``Nat
  | .ofBool .. => mkConst ``Bool
  | .ofInt .. => none
  | .ofName .. => none
  | .ofSyntax .. => none

def validateOptionValue (optionName : Name) (decl : OptionDecl) (val : DataValue) : m Unit := do
  unless decl.defValue.sameCtor val do
    throwMistypedOptionValue val decl.defValue
where
  throwMistypedOptionValue (found defVal : DataValue) := do
    match ctorType? defVal with
    | some defValType =>
      let foundType := ctorType? found |>.get!
      throwError "set_option value type mismatch: The value{indentD (toMessageData found)}\nhas type\
        {indentD (toMessageData foundType)}\nbut the option `{optionName}` expects a value of type\
        {indentExpr defValType}"
    | _ => throwUnconfigurable optionName

def elabSetOption (id : Syntax) (val : Syntax) : m Options := do
  let ref ← getRef
  -- For completion purposes, we discard `val` and any later arguments.
  -- We include the first argument (the keyword) for position information in case `id` is `missing`.
  addCompletionInfo <| CompletionInfo.option (ref.setArgs (ref.getArgs[*...3]))
  let optionName := id.getId.eraseMacroScopes
  let decl ← IO.toEIO (fun (ex : IO.Error) => Exception.error ref ex.toString) (getOptionDecl optionName)
  pushInfoLeaf <| .ofOptionInfo { stx := id, optionName, declName := decl.declName }
  let rec setOption (val : DataValue) : m Options := do
    validateOptionValue optionName decl val
    return (← getOptions).set optionName val
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
    if let some ctorType := ctorType? decl.defValue then
      throwError "Unexpected set_option value `{val}`; expected a literal of type `{ctorType}`"
    else
      throwUnconfigurable optionName

end Lean.Elab
