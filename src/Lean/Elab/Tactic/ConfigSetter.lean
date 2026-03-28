/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Elab.Command
public meta import Lean.Elab.Command
public section
namespace Lean.Elab
open Command Meta

-- We automatically disable the following option for `macro`s but the subsequent `def` both contains
-- a quotation and is called only by `macro`s, so we disable the option for it manually. Note that
-- we can't use `in` as it is parsed as a single command and so the option would not influence the
-- parser.
set_option internal.parseQuotWithCurrentStage false

/--
Generates a function `setterName` for updating the `Bool` and `Nat` fields
of the structure `struct`.
This is a very simple implementation. There is no support for subobjects.
-/
meta def mkConfigSetter (doc? : Option (TSyntax ``Parser.Command.docComment))
    (setterName struct : Ident) : CommandElabM Unit := do
  let structName ← resolveGlobalConstNoOverload struct
  let .inductInfo val ← getConstInfo structName
    | throwErrorAt struct "`{structName}` is not s structure"
  unless val.levelParams.isEmpty do
    throwErrorAt struct "`{structName}` is universe polymorphic"
  unless val.numIndices == 0 && val.numParams == 0 do
    throwErrorAt struct "`{structName}` must not be parametric"
  let env ← getEnv
  let some structInfo := getStructureInfo? env structName
    | throwErrorAt struct "`{structName}` is not a structure"
  let code : Term ← liftTermElabM do
    let mut code : Term ← `(throwError "invalid configuration option `{fieldName}`")
    for fieldInfo in structInfo.fieldInfo do
      if fieldInfo.subobject?.isSome then continue -- ignore subobject's
      let projInfo ← getConstInfo fieldInfo.projFn
      let fieldType ← forallTelescope projInfo.type fun _ body => pure body
      -- **Note**: We only support `Nat` and `Bool` fields
      let fieldIdent : Ident := mkCIdent fieldInfo.fieldName
      if fieldType.isConstOf ``Nat then
        code ← `(if fieldName == $(quote fieldInfo.fieldName) then do
                   Term.addTermInfo' (← getRef) (← mkConstWithLevelParams $(quote fieldInfo.projFn))
                   return { s with $fieldIdent:ident := (← getNatField) }
                 else $code)
      else if fieldType.isConstOf ``Bool then
        code ← `(if fieldName == $(quote fieldInfo.fieldName) then do
                   Term.addTermInfo' (← getRef) (← mkConstWithLevelParams $(quote fieldInfo.projFn))
                   return { s with $fieldIdent:ident := (← getBoolField) }
                 else $code)
    return code
  let cmd ← `(command|
     $[$doc?:docComment]?
     def $setterName (s : $struct) (fieldName : Name) (val : DataValue) : TermElabM $struct :=
       let getBoolField : TermElabM Bool := do
          let .ofBool b := val | throwError "`{fieldName}` is a Boolean"
          return b
       let getNatField : TermElabM Nat := do
         let .ofNat n := val | throwError "`{fieldName}` is a natural number"
         return n
       $code
  )
  elabCommand cmd

elab (name := elabConfigGetter) doc?:(docComment)? "declare_config_getter" setterName:ident type:ident : command => do
  mkConfigSetter doc? setterName type

end Lean.Elab
